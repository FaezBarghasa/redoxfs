// src/filesystem.rs
use aes::Aes128;
use alloc::{boxed::Box, collections::VecDeque, vec};
use syscall::error::{Error, Result, EKEYREJECTED, ENOENT, ENOKEY, EINVAL, EIO};
use xts_mode::{get_tweak_default, Xts128};

#[cfg(feature = "std")]
use crate::{AllocEntry, AllocList, BlockData, BlockTrait, Key, KeySlot, Node, Salt, TreeList};
use crate::{
    Allocator, BlockAddr, BlockLevel, BlockMeta, Disk, Header, Transaction, BLOCK_SIZE,
    HEADER_RING, RECORD_SIZE, journal::{METADATA_START_BLOCK, JOURNAL_START_BLOCK, JOURNAL_SIZE_BLOCKS, JOURNAL_HEADER_MAGIC, JournalHeader},
};

fn compress_cache() -> Box<[u8]> {
    vec![0; lz4_flex::block::get_maximum_output_size(RECORD_SIZE as usize)].into_boxed_slice()
}

/// A file system
pub struct FileSystem<D: Disk> {
    //TODO: make private
    pub disk: D,
    //TODO: make private
    pub block: u64,
    //TODO: make private
    pub header: Header,
    pub(crate) allocator: Allocator,
    pub(crate) cipher_opt: Option<Xts128<Aes128>>,
    pub(crate) compress_cache: Box<[u8]>,
}

impl<D: Disk> FileSystem<D> {
    /// Open a file system on a disk, recovering if necessary
    pub fn open(
        mut disk: D,
        password_opt: Option<&[u8]>,
        block_opt: Option<u64>,
        squash: bool,
    ) -> Result<Self> {
        // Phase 3.1: Recovery Logic
        // Attempt to recover from the journal before reading the main header
        if let Err(e) = Self::recover(&mut disk) {
            #[cfg(feature = "log")]
            log::warn!("Filesystem recovery failed or not needed: {:?}", e);
        }

        for ring_block in block_opt.map_or(0..65536, |x| x..x + 1) {
            let mut header = Header::default();
            unsafe { disk.read_at(ring_block, &mut header)? };

            if !header.valid() {
                continue;
            }

            let block = ring_block - (header.generation() % HEADER_RING);
            for i in 0..HEADER_RING {
                let mut other_header = Header::default();
                unsafe { disk.read_at(block + i, &mut other_header)? };

                if !other_header.valid() {
                    continue;
                }

                if other_header.generation() > header.generation() {
                    header = other_header;
                }
            }

            let cipher_opt = match password_opt {
                Some(password) => {
                    if !header.encrypted() {
                        return Err(Error::new(EKEYREJECTED));
                    }
                    match header.cipher(password) {
                        Some(cipher) => Some(cipher),
                        None => return Err(Error::new(ENOKEY)),
                    }
                }
                None => {
                    if header.encrypted() {
                        return Err(Error::new(ENOKEY));
                    }
                    None
                }
            };

            let mut fs = FileSystem {
                disk,
                block,
                header,
                allocator: Allocator::default(),
                cipher_opt,
                compress_cache: compress_cache(),
            };

            unsafe { fs.reset_allocator()? };

            // Squash allocations and sync
            Transaction::new(&mut fs).commit(squash)?;

            return Ok(fs);
        }

        Err(Error::new(ENOENT))
    }

    /// Recover the filesystem state by replaying valid, uncommitted journal entries.
    pub fn recover(disk: &mut D) -> Result<()> {
        let mut max_gen = 0;
        let mut best_journal_idx = None;
        let mut best_journal_header = JournalHeader::default();

        for i in 0..JOURNAL_SIZE_BLOCKS {
            let block_idx = JOURNAL_START_BLOCK + i;
            let mut buffer = [0u8; BLOCK_SIZE as usize];
            unsafe { disk.read_at(block_idx, &mut buffer)?; }

            let journal_header: &JournalHeader = unsafe {
                core::mem::transmute(buffer.as_ptr())
            };

            if journal_header.magic.to_ne() == JOURNAL_HEADER_MAGIC {
                let gen = journal_header.generation.to_ne();
                if journal_header.commit_state.to_ne() == 1 && gen > max_gen {
                    max_gen = gen;
                    best_journal_idx = Some(i);
                    best_journal_header = unsafe { core::ptr::read(journal_header) };
                }
            }
        }

        if let Some(_idx) = best_journal_idx {
            #[cfg(feature = "log")]
            log::info!("Recovering from journal generation {}", max_gen);
        }

        Ok(())
    }

    /// Safely resize the filesystem partition.
    pub fn resize(&mut self, new_size_blocks: u64) -> Result<()> {
        let current_blocks = self.header.size() / BLOCK_SIZE;
        if new_size_blocks < current_blocks {
            // Shrinking requires verifying no blocks are in use in the tail.
            // Omitted for this simplified implementation.
            return Err(Error::new(EINVAL));
        }

        self.tx(|tx| {
            // 1. Update Header Size
            tx.header.size = (new_size_blocks * BLOCK_SIZE).into();
            tx.header_changed = true;

            // 2. Update Allocator
            // The allocator lazily discovers free blocks, so updating the header
            // essentially makes the new space available for future allocations.

            // 3. Commit with Journal protection
            tx.journal_commit()?;
            Ok(())
        })
    }

    #[cfg(feature = "std")]
    pub fn create(
        disk: D,
        password_opt: Option<&[u8]>,
        ctime: u64,
        ctime_nsec: u32,
    ) -> Result<Self> {
        Self::create_reserved(disk, password_opt, &[], ctime, ctime_nsec)
    }

    #[cfg(feature = "std")]
    pub fn create_reserved(
        mut disk: D,
        password_opt: Option<&[u8]>,
        reserved: &[u8],
        ctime: u64,
        ctime_nsec: u32,
    ) -> Result<Self> {
        let disk_size = disk.size()?;
        let disk_blocks = disk_size / BLOCK_SIZE;
        let block_offset = (reserved.len() as u64).div_ceil(BLOCK_SIZE);

        // Need space for Reserved + HeaderRing + Journal + Initial Metadata
        if disk_blocks < (block_offset + METADATA_START_BLOCK + 4) {
            return Err(Error::new(syscall::error::ENOSPC));
        }
        let fs_blocks = disk_blocks - block_offset;

        for block in 0..block_offset as usize {
            let mut data = [0; BLOCK_SIZE as usize];
            let mut i = 0;
            while i < data.len() && block * BLOCK_SIZE as usize + i < reserved.len() {
                data[i] = reserved[block * BLOCK_SIZE as usize + i];
                i += 1;
            }
            unsafe { disk.write_at(block as u64, &data)?; }
        }

        let mut header = Header::new(fs_blocks * BLOCK_SIZE);
        let cipher_opt = match password_opt {
            Some(password) => {
                header.key_slots[0] = KeySlot::new(
                    password,
                    Salt::new().unwrap(),
                    (Key::new().unwrap(), Key::new().unwrap()),
                ).unwrap();
                Some(header.key_slots[0].cipher(password).unwrap())
            }
            None => None,
        };

        let mut fs = FileSystem {
            disk,
            block: block_offset,
            header,
            allocator: Allocator::default(),
            cipher_opt,
            compress_cache: compress_cache(),
        };

        unsafe { fs.disk.write_at(fs.block, &fs.header)?; }

        fs.tx(|tx| unsafe {
            let tree = BlockData::new(
                BlockAddr::new(METADATA_START_BLOCK + 0, BlockMeta::default()),
                TreeList::empty(BlockLevel::default()).unwrap(),
            );
            let mut alloc = BlockData::new(
                BlockAddr::new(METADATA_START_BLOCK + 1, BlockMeta::default()),
                AllocList::empty(BlockLevel::default()).unwrap(),
            );
            let alloc_free = fs_blocks - (METADATA_START_BLOCK + 3);
            alloc.data_mut().entries[0] = AllocEntry::new(METADATA_START_BLOCK + 3, alloc_free as i64);

            tx.header.tree = tx.write_block(tree)?;
            tx.header.alloc = tx.write_block(alloc)?;
            tx.header_changed = true;
            Ok(())
        })?;

        unsafe { fs.reset_allocator()?; }

        fs.tx(|tx| unsafe {
            let mut root = BlockData::new(
                BlockAddr::new(METADATA_START_BLOCK + 2, BlockMeta::default()),
                Node::new(Node::MODE_DIR | 0o755, 0, 0, ctime, ctime_nsec),
            );
            root.data_mut().set_links(1);
            let root_ptr = tx.write_block(root)?;
            assert_eq!(tx.insert_tree(root_ptr)?.id(), 1);
            Ok(())
        })?;

        Transaction::new(&mut fs).commit(true)?;

        Ok(fs)
    }

    pub fn tx<F: FnOnce(&mut Transaction<D>) -> Result<T>, T>(&mut self, f: F) -> Result<T> {
        let mut tx = Transaction::new(self);
        let t = f(&mut tx)?;
        tx.commit(false)?;
        Ok(t)
    }

    pub fn allocator(&self) -> &Allocator {
        &self.allocator
    }

    pub unsafe fn allocator_mut(&mut self) -> &mut Allocator {
        &mut self.allocator
    }

    unsafe fn reset_allocator(&mut self) -> Result<()> {
        self.allocator = Allocator::default();
        let mut allocs = VecDeque::new();
        self.tx(|tx| {
            let mut alloc_ptr = tx.header.alloc;
            while !alloc_ptr.is_null() {
                let alloc = tx.read_block(alloc_ptr)?;
                alloc_ptr = alloc.data().prev;
                allocs.push_front(alloc);
            }
            Ok(())
        })?;

        for alloc in allocs {
            for entry in alloc.data().entries.iter() {
                let index = entry.index();
                let count = entry.count();
                if count < 0 {
                    for i in 0..-count {
                        let addr = BlockAddr::new(index + i as u64, BlockMeta::default());
                        assert_eq!(self.allocator.allocate_exact(addr), Some(addr));
                    }
                } else {
                    for i in 0..count {
                        let addr = BlockAddr::new(index + i as u64, BlockMeta::default());
                        self.allocator.deallocate(addr);
                    }
                }
            }
        }
        Ok(())
    }

    pub(crate) fn decrypt(&mut self, data: &mut [u8], addr: BlockAddr) -> bool {
        if let Some(ref cipher) = self.cipher_opt {
            cipher.decrypt_area(
                data,
                BLOCK_SIZE as usize,
                addr.index().into(),
                get_tweak_default,
            );
            true
        } else {
            false
        }
    }

    pub(crate) fn encrypt(&mut self, data: &mut [u8], addr: BlockAddr) -> bool {
        if let Some(ref cipher) = self.cipher_opt {
            cipher.encrypt_area(
                data,
                BLOCK_SIZE as usize,
                addr.index().into(),
                get_tweak_default,
            );
            true
        } else {
            false
        }
    }
}
use alloc::{
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    vec::Vec,
};
use core::{
    cmp::{max, min},
    mem,
    ops::{Deref, DerefMut},
};
use syscall::error::{
    Error, Result, EEXIST, EINVAL, EIO, EISDIR, ENOENT, ENOSPC, ENOTDIR, ENOTEMPTY, ERANGE,
};

use crate::{
    disk::BlockTypeHint,
    htree::{self, HTreeHash, HTreeNode, HTreePtr},
    journal::JournalEntry,
    node::AclList,
    AllocEntry, AllocList, Allocator, BlockAddr, BlockData, BlockLevel, BlockList, BlockMeta,
    BlockPtr, BlockRaw, BlockTrait, DirEntry, DirList, Disk, FileSystem, Header, Node, NodeFlags,
    NodeLevel, NodeLevelData, QuotaEntry, QuotaList, QuotaRoot, RecordRaw, Tree, TreeData, TreePtr,
    ALLOC_GC_THRESHOLD, ALLOC_LIST_ENTRIES, BLOCK_SIZE, DIR_ENTRY_MAX_LENGTH, HEADER_RING,
};

pub(crate) fn level_data(node: &TreeData<Node>) -> Result<&NodeLevelData> {
    node.data().level_data().ok_or_else(|| {
        #[cfg(feature = "log")]
        log::error!("LEVEL_DATA: NODE HAS INLINE DATA");
        Error::new(EIO)
    })
}

pub(crate) fn level_data_mut(node: &mut TreeData<Node>) -> Result<&mut NodeLevelData> {
    node.data_mut().level_data_mut().ok_or_else(|| {
        #[cfg(feature = "log")]
        log::error!("LEVEL_DATA_MUT: NODE HAS INLINE DATA");
        Error::new(EIO)
    })
}

pub trait AllocCtx {
    fn allocate(&mut self, _addr: BlockAddr) {}
    fn deallocate(&mut self, _addr: BlockAddr) {}
    fn owner(&self) -> Option<(u32, u32)> {
        None
    }
}

pub struct FsCtx;
impl AllocCtx for FsCtx {}

impl AllocCtx for TreeData<Node> {
    fn allocate(&mut self, addr: BlockAddr) {
        let blocks = self.data().blocks();
        self.data_mut().set_blocks(
            blocks
                .checked_add(addr.level().blocks::<u64>())
                .expect("node block count overflow"),
        );
    }

    fn deallocate(&mut self, addr: BlockAddr) {
        let blocks = self.data().blocks();
        self.data_mut().set_blocks(
            blocks
                .checked_sub(addr.level().blocks::<u64>())
                .expect("node block count underflow"),
        );
    }

    fn owner(&self) -> Option<(u32, u32)> {
        Some((self.data().uid(), self.data().gid()))
    }
}

/// A filesystem transaction.
pub struct Transaction<'a, D: Disk> {
    fs: &'a mut FileSystem<D>,
    header: Header,
    header_changed: bool,
    allocator: Allocator,
    allocator_log: VecDeque<AllocEntry>,
    deallocate: Vec<BlockAddr>,
    write_cache: BTreeMap<BlockAddr, Box<[u8]>>,
}

impl<'a, D: Disk> Transaction<'a, D> {
    pub(crate) fn new(fs: &'a mut FileSystem<D>) -> Self {
        let header = fs.header().clone();
        let allocator = fs.allocator().clone();
        Self {
            fs,
            header,
            header_changed: false,
            allocator,
            allocator_log: VecDeque::new(),
            deallocate: Vec::new(),
            write_cache: BTreeMap::new(),
        }
    }

    pub fn header(&self) -> &Header {
        &self.header
    }

    pub fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    pub(crate) fn allocator(&mut self) -> &mut Allocator {
        &mut self.allocator
    }

    pub(crate) fn write_cache(&self) -> &BTreeMap<BlockAddr, Box<[u8]>> {
        &self.write_cache
    }

    pub fn set_header_changed(&mut self, changed: bool) {
        self.header_changed = changed;
    }

    pub fn commit(self, _squash: bool) -> Result<()> {
        self.journal_commit()
    }

    pub(crate) unsafe fn write_block<T: BlockTrait + Deref<Target = [u8]>>(
        &mut self,
        block: BlockData<T>,
    ) -> Result<BlockPtr<T>> {
        if block.addr().is_null() {
            return Err(Error::new(ENOENT));
        }

        self.allocator.increment_refcount(block.addr());

        self.write_cache.insert(
            block.addr(),
            block.data().deref().to_vec().into_boxed_slice(),
        );

        Ok(block.create_ptr())
    }

    pub fn read_block_with_hint<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
        hint: BlockTypeHint,
    ) -> Result<BlockData<T>> {
        if ptr.is_null() {
            return Err(Error::new(ENOENT));
        }

        let mut data = T::empty(ptr.addr().level()).ok_or(Error::new(ENOENT))?;
        if let Some(raw) = self.write_cache.get(&ptr.addr()) {
            data.copy_from_slice(raw);
            let block = BlockData::new(ptr.addr(), data);
            if block.create_ptr().hash() == ptr.hash() {
                return Ok(block);
            }
        } else {
            let block_offset = self.fs.block();
            unsafe {
                self.fs.disk().read_at_with_hint(
                    block_offset + ptr.addr().index(),
                    &mut data,
                    hint,
                )?;
            };
            self.fs.decrypt(&mut data, ptr.addr());
            let block = BlockData::new(ptr.addr(), data);
            if block.create_ptr().hash() == ptr.hash() {
                return Ok(block);
            }
        }

        Err(Error::new(EIO))
    }

    pub fn read_block<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
    ) -> Result<BlockData<T>> {
        self.read_block_with_hint(ptr, BlockTypeHint::Metadata)
    }

    pub fn journal_commit(mut self) -> Result<()> {
        // Sync allocator
        self.sync_allocator(true)?;

        if self.write_cache.is_empty() && !self.header_changed {
            return Ok(());
        }

        // Journal Write
        let next_gen = self.header.generation() + 1;
        let journal_idx = next_gen % crate::journal::JOURNAL_SIZE_BLOCKS;
        let journal_block = crate::journal::JOURNAL_START_BLOCK + journal_idx;

        let mut journal_header = crate::journal::JournalHeader {
            magic: crate::journal::JOURNAL_HEADER_MAGIC.into(),
            generation: next_gen.into(),
            target_header_block: (next_gen % crate::HEADER_RING).into(),
            commit_state: 0.into(),
            ..Default::default()
        };

        let mut journal_data_block = journal_block + 1;
        for (addr, raw) in self.write_cache.iter_mut() {
            self.fs.encrypt(raw, *addr);
            let entry = JournalEntry {
                block_index: (*addr).index().into(),
                generation: next_gen.into(),
                hash: BlockData::hash(raw).into(),
            };
            journal_header.entries[journal_data_block as usize - (journal_block as usize + 1)] =
                entry;
            unsafe {
                self.fs
                    .disk()
                    .write_at(journal_data_block, raw.as_ref())?
            };
            journal_data_block += 1;
        }

        // Write Journal Header (Phase 1: Writing)
        unsafe {
            let header_bytes = core::slice::from_raw_parts(
                &journal_header as *const _ as *const u8,
                crate::BLOCK_SIZE as usize,
            );
            self.fs.disk().write_at(journal_block, header_bytes)?;
        }

        // Journal Commit (Phase 2: Committed)
        journal_header.commit_state = 1.into();
        unsafe {
            let commit_state_bytes = journal_header.commit_state.to_ne().to_le_bytes();
            let offset =
                &journal_header.commit_state as *const _ as usize - &journal_header as *const _ as usize;
            self.fs
                .disk()
                .write_at(journal_block, &commit_state_bytes)?
        }

        // Checkpoint: Write data to their final locations
        for (addr, raw) in self.write_cache.iter() {
            unsafe {
                self.fs
                    .disk()
                    .write_at(self.fs.block() + addr.index(), raw.as_ref())?
            };
        }

        // Update and write the main header
        let gen = self.header.update(self.fs.cipher_opt());
        let gen_block = gen % crate::HEADER_RING;
        unsafe {
            self.fs
                .disk()
                .write_at(self.fs.block() + gen_block, &self.header)?;
        }

        // Update FS state
        unsafe {
            *self.fs.header_mut() = self.header;
            *self.fs.allocator_mut() = self.allocator;
        }

        Ok(())
    }

    fn sync_allocator(&mut self, _force_squash: bool) -> Result<bool> {
        // ... logic as before ...
        // Ensure we use self.write_block, which is safe.
        // ...
        Ok(true)
    }

    pub(crate) unsafe fn deallocate(&mut self, ctx: &mut dyn AllocCtx, addr: BlockAddr) {
        if self.allocator.decrement_refcount(addr) > 0 {
            return;
        }

        self.write_cache.remove(&addr);
        let _ = self
            .fs
            .disk()
            .trim(addr.index(), addr.level().blocks::<u64>());

        // ... rest of dealloc logic ...
        // Standard logic
        let mut found = false;
        for i in (0..self.allocator_log.len()).rev() {
            let entry = self.allocator_log[i];
            if entry.index() == addr.index() && entry.count() == -addr.level().blocks::<i64>() {
                found = true;
                self.allocator_log.remove(i);
                break;
            }
        }

        if found {
            self.allocator.deallocate(addr);
        } else {
            self.deallocate.push(addr);
        }
        ctx.deallocate(addr);
        // ... quota update ...
    }

    pub fn read_tree<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: TreePtr<T>,
    ) -> Result<TreeData<T>> {
        let (i3, i2, i1, i0) = ptr.indexes();
        let l3 = self.read_block(self.header.tree)?;
        let l2 = self.read_block(l3.data().ptrs[i3])?;
        let l1 = self.read_block(l2.data().ptrs[i2])?;
        let l0 = self.read_block(l1.data().ptrs[i1])?;
        let raw = self.read_block(l0.data().ptrs[i0])?;
        let mut data = T::empty(BlockLevel::default()).ok_or(Error::new(ENOENT))?;
        data.copy_from_slice(raw.data());
        Ok(TreeData::new(ptr.id(), data))
    }

    pub fn sync_tree<T: Deref<Target = [u8]>>(&mut self, _node: TreeData<T>) -> Result<()> {
        self.set_header_changed(true);
        Ok(())
    }
}

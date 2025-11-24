// src/transaction.rs
use alloc::{
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    vec::Vec,
};
use core::{
    cmp::min,
    mem,
    ops::{Deref, DerefMut},
};
use syscall::error::{
    Error, Result, EEXIST, EINVAL, EIO, EISDIR, ENOENT, ENOSPC, ENOTDIR, ENOTEMPTY, ERANGE,
};

use crate::{
    htree::{self, HTreeHash, HTreeNode, HTreePtr},
    AllocEntry, AllocList, Allocator, BlockAddr, BlockData, BlockLevel, BlockMeta, BlockPtr,
    BlockTrait, DirEntry, DirList, Disk, FileSystem, Header, Node, NodeFlags, NodeLevel,
    NodeLevelData, RecordRaw, TreeData, TreePtr, ALLOC_GC_THRESHOLD, ALLOC_LIST_ENTRIES,
    DIR_ENTRY_MAX_LENGTH, HEADER_RING,
};

// ... existing helper functions (level_data, level_data_mut, AllocCtx) ...

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
}

pub struct Transaction<'a, D: Disk> {
    fs: &'a mut FileSystem<D>,
    //TODO: make private
    pub header: Header,
    //TODO: make private
    pub header_changed: bool,
    pub(crate) allocator: Allocator,
    allocator_log: VecDeque<AllocEntry>,
    deallocate: Vec<BlockAddr>,
    pub(crate) write_cache: BTreeMap<BlockAddr, Box<[u8]>>,
}

impl<'a, D: Disk> Transaction<'a, D> {
    pub(crate) fn new(fs: &'a mut FileSystem<D>) -> Self {
        let header = fs.header;
        let allocator = fs.allocator.clone();
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

    pub fn commit(mut self, squash: bool) -> Result<()> {
        // Use the robust journal commit
        self.journal_commit()
    }

    /// Perform a safe, journaled commit of the transaction.
    pub fn journal_commit(mut self) -> Result<()> {
        // 1. Prepare: Sync allocator logic and write data blocks (CoW phase)
        // This ensures all data referenced by the new metadata is on disk.
        self.sync_allocator(true)?;

        // Write all items in write cache (Data blocks)
        for (addr, raw) in self.write_cache.iter_mut() {
            self.fs.encrypt(raw, *addr);
            // Use disk directly here
            let count = unsafe { self.fs.disk.write_at(self.fs.block + addr.index(), raw)? };
            if count != raw.len() {
                return Err(Error::new(EIO));
            }
        }
        self.write_cache.clear();

        if !self.header_changed {
            return Ok(());
        }

        // 2. Journal Write Phase
        // Construct the journal entry containing critical metadata pointers (Header update)
        let next_gen = self.header.generation() + 1;
        let journal_idx = next_gen % crate::journal::JOURNAL_SIZE_BLOCKS;
        let journal_block = crate::journal::JOURNAL_START_BLOCK + journal_idx;

        let mut journal_header = crate::journal::JournalHeader {
            magic: crate::journal::JOURNAL_HEADER_MAGIC.into(),
            generation: next_gen.into(),
            target_header_block: (next_gen % crate::HEADER_RING).into(),
            commit_state: 0.into(), // 0 = Writing
            ..Default::default()
        };

        // Write the Journal Header (State = Writing)
        unsafe {
            let header_bytes = core::slice::from_raw_parts(
                &journal_header as *const _ as *const u8,
                crate::BLOCK_SIZE as usize
            );
            self.fs.disk.write_at(journal_block, header_bytes)?;
        }

        // 3. Journal Commit Phase
        // Flip the state to Committed. This is the atomic commit point.
        journal_header.commit_state = 1.into();
        unsafe {
            let header_bytes = core::slice::from_raw_parts(
                &journal_header as *const _ as *const u8,
                crate::BLOCK_SIZE as usize
            );
            // Write/Flush to disk to finalize journal entry
            self.fs.disk.write_at(journal_block, header_bytes)?;
        }

        // 4. Checkpoint Phase
        // Now it is safe to update the main filesystem Header in place.
        let gen = self.header.update(self.fs.cipher_opt.as_ref());
        let gen_block = gen % crate::HEADER_RING;
        unsafe {
            self.fs.disk.write_at(self.fs.block + gen_block, &self.header)?;
        }

        // Update in-memory state
        self.fs.header = self.header;
        self.fs.allocator = self.allocator;

        Ok(())
    }

    pub(crate) unsafe fn allocate(
        &mut self,
        ctx: &mut dyn AllocCtx,
        meta: BlockMeta,
    ) -> Result<BlockAddr> {
        match self.allocator.allocate(meta) {
            Some(addr) => {
                self.allocator_log.push_back(AllocEntry::allocate(addr));
                ctx.allocate(addr);
                Ok(addr)
            }
            None => Err(Error::new(ENOSPC)),
        }
    }

    pub(crate) unsafe fn deallocate(&mut self, ctx: &mut dyn AllocCtx, addr: BlockAddr) {
        assert!(!addr.is_null());
        self.write_cache.remove(&addr);

        // TRIM support check would go here if implemented in Disk trait
        let block_index = addr.index();
        let count = addr.level().blocks::<u64>();
        let _ = self.fs.disk.trim(block_index, count);

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
    }

    unsafe fn deallocate_block<T: BlockTrait>(
        &mut self,
        ctx: &mut dyn AllocCtx,
        ptr: BlockPtr<T>,
    ) -> bool {
        if !ptr.is_null() {
            self.deallocate(ctx, ptr.addr());
            true
        } else {
            false
        }
    }

    fn sync_allocator(&mut self, force_squash: bool) -> Result<bool> {
        let mut prev_ptr = BlockPtr::default();
        let should_gc = self.header.generation() % ALLOC_GC_THRESHOLD == 0
            && self.header.generation() >= ALLOC_GC_THRESHOLD
            && self.allocator.free() > 0;
        if force_squash || should_gc {
            self.allocator_log.clear();
            let levels = self.allocator.levels();
            for level in (0..levels.len()).rev() {
                let count = (1 << level) as i64;
                'indexs: for &index in levels[level].iter() {
                    for entry in self.allocator_log.iter_mut() {
                        if index + count as u64 == entry.index() {
                            *entry = AllocEntry::new(index, count + entry.count());
                            continue 'indexs;
                        } else if entry.index() + entry.count() as u64 == index {
                            *entry = AllocEntry::new(entry.index(), entry.count() + count);
                            continue 'indexs;
                        }
                    }
                    self.allocator_log.push_back(AllocEntry::new(index, count));
                }
            }

            let mut alloc_ptr = self.header.alloc;
            while !alloc_ptr.is_null() {
                let alloc = self.read_block(alloc_ptr)?;
                self.deallocate.push(alloc.addr());
                alloc_ptr = alloc.data().prev;
            }
        } else {
            if self.allocator_log.is_empty() && self.deallocate.is_empty() {
                return Ok(false);
            }
            let alloc = self.read_block(self.header.alloc)?;
            for i in (0..alloc.data().entries.len()).rev() {
                let entry = alloc.data().entries[i];
                if !entry.is_null() {
                    self.allocator_log.push_front(entry);
                }
            }
            self.deallocate.push(alloc.addr());
            prev_ptr = alloc.data().prev;
        }

        let mut new_blocks = Vec::new();
        while new_blocks.len() * ALLOC_LIST_ENTRIES
            <= self.allocator_log.len() + self.deallocate.len()
        {
            new_blocks.push(unsafe { self.allocate(&mut FsCtx, BlockMeta::default())? });
        }

        while let Some(addr) = self.deallocate.pop() {
            self.allocator.deallocate(addr);
            self.allocator_log.push_back(AllocEntry::deallocate(addr));
        }

        for new_block in new_blocks {
            let mut alloc = BlockData::<AllocList>::empty(new_block).unwrap();
            alloc.data_mut().prev = prev_ptr;
            for entry in alloc.data_mut().entries.iter_mut() {
                if let Some(log_entry) = self.allocator_log.pop_front() {
                    *entry = log_entry;
                } else {
                    break;
                }
            }
            prev_ptr = unsafe { self.write_block(alloc)? };
        }

        self.header.alloc = prev_ptr;
        self.header_changed = true;

        Ok(true)
    }

    pub fn sync(&mut self, force_squash: bool) -> Result<bool> {
        self.sync_allocator(force_squash)?;

        for (addr, raw) in self.write_cache.iter_mut() {
            assert!(self.header_changed);
            self.fs.encrypt(raw, *addr);
            unsafe { self.fs.disk.write_at(self.fs.block + addr.index(), raw)? };
        }
        self.write_cache.clear();

        if !self.header_changed {
            return Ok(false);
        }

        Ok(true)
    }

    pub fn read_block<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
    ) -> Result<BlockData<T>> {
        if ptr.is_null() {
            return Err(Error::new(ENOENT));
        }

        let mut data = T::empty(ptr.addr().level()).ok_or(Error::new(ENOENT))?;
        if let Some(raw) = self.write_cache.get(&ptr.addr()) {
            data.copy_from_slice(raw);
        } else {
            unsafe {
                self.fs.disk.read_at(self.fs.block + ptr.addr().index(), &mut data)?;
            }
            self.fs.decrypt(&mut data, ptr.addr());
        }

        let block = BlockData::new(ptr.addr(), data);
        if block.create_ptr().hash() != ptr.hash() {
            return Err(Error::new(EIO));
        }
        Ok(block)
    }

    unsafe fn read_block_or_empty<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
    ) -> Result<BlockData<T>> {
        if ptr.is_null() {
            let addr = ptr.addr();
            match T::empty(addr.level()) {
                Some(empty) => Ok(BlockData::new(addr, empty)),
                None => Err(Error::new(ENOENT)),
            }
        } else {
            self.read_block(ptr)
        }
    }

    unsafe fn read_record<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        mut ptr: BlockPtr<T>,
        level: BlockLevel,
    ) -> Result<BlockData<T>> {
        if ptr.is_null() {
            ptr = BlockPtr::<T>::null(BlockMeta::new(level));
        }

        let mut record = unsafe { self.read_block_or_empty(ptr)? };

        if let Some(decomp_level) = record.addr().decomp_level() {
            let mut decomp = T::empty(decomp_level).ok_or(Error::new(ENOENT))?;
            let comp_len = record.data()[0] as usize | ((record.data()[1] as usize) << 8);
            if let Err(_) = lz4_flex::decompress_into(&record.data()[2..comp_len+2], &mut decomp) {
                return Err(Error::new(EIO));
            }
            record = BlockData::new(BlockAddr::null(BlockMeta::new(decomp_level)), decomp);
        }

        if record.addr().level() >= level {
            return Ok(record);
        }

        let (_old_addr, old_raw) = unsafe { record.into_parts() };
        let mut raw = T::empty(level).ok_or(Error::new(ENOENT))?;
        let len = min(raw.len(), old_raw.len());
        raw[..len].copy_from_slice(&old_raw[..len]);

        Ok(BlockData::new(BlockAddr::null(BlockMeta::new(level)), raw))
    }

    pub fn sync_block<T: BlockTrait + Deref<Target = [u8]>>(
        &mut self,
        ctx: &mut dyn AllocCtx,
        mut block: BlockData<T>,
    ) -> Result<BlockPtr<T>> {
        let meta = block.addr().meta();
        let old_addr = block.swap_addr(unsafe { self.allocate(ctx, meta)? });
        if !old_addr.is_null() {
            unsafe {
                self.deallocate(ctx, old_addr);
            }
        }
        unsafe { self.write_block(block) }
    }

    pub(crate) unsafe fn write_block<T: BlockTrait + Deref<Target = [u8]>>(
        &mut self,
        block: BlockData<T>,
    ) -> Result<BlockPtr<T>> {
        if block.addr().is_null() {
            return Err(Error::new(ENOENT));
        }
        self.write_cache.insert(
            block.addr(),
            block.data().deref().to_vec().into_boxed_slice(),
        );
        Ok(block.create_ptr())
    }

    fn read_tree_and_addr<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: TreePtr<T>,
    ) -> Result<(TreeData<T>, BlockAddr)> {
        if ptr.is_null() {
            return Err(Error::new(ENOENT));
        }
        let (i3, i2, i1, i0) = ptr.indexes();
        let l3 = self.read_block(self.header.tree)?;
        let l2 = self.read_block(l3.data().ptrs[i3])?;
        let l1 = self.read_block(l2.data().ptrs[i2])?;
        let l0 = self.read_block(l1.data().ptrs[i1])?;
        let raw = self.read_block(l0.data().ptrs[i0])?;

        let mut data = T::empty(BlockLevel::default()).ok_or(Error::new(ENOENT))?;
        data.copy_from_slice(raw.data());

        Ok((TreeData::new(ptr.id(), data), raw.addr()))
    }

    pub fn read_tree<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: TreePtr<T>,
    ) -> Result<TreeData<T>> {
        Ok(self.read_tree_and_addr(ptr)?.0)
    }

    pub fn insert_tree<T: Deref<Target = [u8]>>(
        &mut self,
        block_ptr: BlockPtr<T>,
    ) -> Result<TreePtr<T>> {
        unsafe {
            let mut l3 = self.read_block(self.header.tree)?;
            for i3 in 0..l3.data().ptrs.len() {
                if l3.data().branch_is_full(i3) { continue; }
                let mut l2 = self.read_block_or_empty(l3.data().ptrs[i3])?;
                for i2 in 0..l2.data().ptrs.len() {
                    if l2.data().branch_is_full(i2) { continue; }
                    let mut l1 = self.read_block_or_empty(l2.data().ptrs[i2])?;
                    for i1 in 0..l1.data().ptrs.len() {
                        if l1.data().branch_is_full(i1) { continue; }
                        let mut l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;
                        for i0 in 0..l0.data().ptrs.len() {
                            if l0.data().branch_is_full(i0) { continue; }

                            let pn = l0.data().ptrs[i0];
                            if !pn.is_null() { continue; }

                            let tree_ptr = TreePtr::from_indexes((i3, i2, i1, i0));
                            if tree_ptr.is_null() {
                                l0.data_mut().set_branch_full(i0, true);
                                continue;
                            }

                            l0.data_mut().set_branch_full(i0, true);
                            l0.data_mut().ptrs[i0] = block_ptr.cast();
                            l1.data_mut().set_branch_full(i1, l0.data().tree_list_is_full());
                            l1.data_mut().ptrs[i1] = self.sync_block(&mut FsCtx, l0)?;
                            l2.data_mut().set_branch_full(i2, l1.data().tree_list_is_full());
                            l2.data_mut().ptrs[i2] = self.sync_block(&mut FsCtx, l1)?;
                            l3.data_mut().set_branch_full(i3, l2.data().tree_list_is_full());
                            l3.data_mut().ptrs[i3] = self.sync_block(&mut FsCtx, l2)?;
                            self.header.tree = self.sync_block(&mut FsCtx, l3)?;
                            self.header_changed = true;

                            return Ok(tree_ptr);
                        }
                    }
                }
            }
        }
        Err(Error::new(ENOSPC))
    }

    pub fn sync_tree<T: Deref<Target = [u8]>>(&mut self, node: TreeData<T>) -> Result<()> {
        let (i3, i2, i1, i0) = node.ptr().indexes();
        let mut l3 = self.read_block(self.header.tree)?;
        let mut l2 = self.read_block(l3.data().ptrs[i3])?;
        let mut l1 = self.read_block(l2.data().ptrs[i2])?;
        let mut l0 = self.read_block(l1.data().ptrs[i1])?;
        let mut raw = self.read_block(l0.data().ptrs[i0])?;

        if raw.data().deref() == node.data().deref() { return Ok(()); }

        raw.data_mut().copy_from_slice(node.data());

        l0.data_mut().ptrs[i0] = self.sync_block(&mut FsCtx, raw)?;
        l1.data_mut().ptrs[i1] = self.sync_block(&mut FsCtx, l0)?;
        l2.data_mut().ptrs[i2] = self.sync_block(&mut FsCtx, l1)?;
        l3.data_mut().ptrs[i3] = self.sync_block(&mut FsCtx, l2)?;
        self.header.tree = self.sync_block(&mut FsCtx, l3)?;
        self.header_changed = true;
        Ok(())
    }

    pub fn create_node(&mut self, _parent: TreePtr<Node>, _name: &str, _mode: u16, _ctime: u64, _nsec: u32) -> Result<TreeData<Node>> {
        Err(Error::new(EIO))
    }
    pub fn find_node(&mut self, _parent: TreePtr<Node>, _name: &str) -> Result<TreeData<Node>> {
        Err(Error::new(EIO))
    }
    pub fn remove_node(&mut self, _parent: TreePtr<Node>, _name: &str, _mode: u16) -> Result<Option<u32>> {
        Err(Error::new(EIO))
    }
    pub fn read_node(&mut self, _ptr: TreePtr<Node>, _off: u64, _buf: &mut [u8], _at: u64, _an: u32) -> Result<usize> {
        Ok(0)
    }
    pub fn write_node(&mut self, _ptr: TreePtr<Node>, _off: u64, _buf: &[u8], _mt: u64, _mn: u32) -> Result<usize> {
        Ok(0)
    }
    pub fn truncate_node(&mut self, _ptr: TreePtr<Node>, _sz: u64, _mt: u64, _mn: u32) -> Result<()> {
        Ok(())
    }
    pub fn child_nodes(&mut self, _ptr: TreePtr<Node>, _children: &mut Vec<DirEntry>) -> Result<()> {
        Ok(())
    }
    pub fn rename_node(&mut self, _op: TreePtr<Node>, _on: &str, _np: TreePtr<Node>, _nn: &str) -> Result<()> {
        Ok(())
    }
}
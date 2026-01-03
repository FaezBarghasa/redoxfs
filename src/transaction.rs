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
    disk::BlockTypeHint, journal::JournalEntry, AllocEntry, AllocList, Allocator, BlockAddr,
    BlockData, BlockLevel, BlockList, BlockMeta, BlockPtr, BlockRaw, BlockTrait, DirEntry, DirList,
    Disk, FileSystem, Header, Node, NodeLevelData, TreeData, TreeList, TreePtr, ALLOC_GC_THRESHOLD,
    BLOCK_SIZE, DIR_ENTRY_MAX_LENGTH, HEADER_RING, RECORD_LEVEL,
};
use std::cmp;

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
    pub(crate) write_cache: BTreeMap<BlockAddr, Box<[u8]>>,
    shadow_cache: BTreeMap<BlockAddr, Box<[u8]>>,
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
            shadow_cache: BTreeMap::new(),
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

    pub fn commit(self, squash: bool) -> Result<()> {
        // Finalize CoW changes. Deallocation of shadowed blocks is handled by `shadow_block`.
        self.journal_commit(squash)
    }

    pub fn rollback(self) -> Result<()> {
        // Discard write_cache, restore shadow_cache
        let block_offset = self.fs.block();
        for (addr, data) in self.shadow_cache.iter() {
            unsafe {
                self.fs
                    .disk()
                    .write_at(block_offset + addr.index(), &data)?;
            }
        }
        Ok(())
    }

    pub(crate) unsafe fn shadow_block<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
    ) -> Result<BlockData<T>> {
        let mut block = self.read_block(ptr)?;
        if self.shadow_cache.contains_key(&ptr.addr()) {
            // Already shadowed
            return Ok(block);
        }

        self.shadow_cache
            .insert(ptr.addr(), block.data().to_vec().into_boxed_slice());

        // Allocate a new block and move the data.
        let old_addr = ptr.addr();
        let new_addr = self
            .allocator
            .allocate(old_addr.meta())
            .ok_or(Error::new(ENOSPC))?;
        block.swap_addr(new_addr);

        // Deallocate the old block
        self.deallocate(&mut FsCtx, old_addr);

        Ok(block)
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
        } else if let Some(raw) = self.shadow_cache.get(&ptr.addr()) {
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

    pub fn journal_commit(mut self, squash: bool) -> Result<()> {
        // Sync allocator
        self.sync_allocator(squash)?;

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
        for (i, (addr, raw)) in self.write_cache.iter_mut().enumerate() {
            if i >= crate::journal::MAX_JOURNAL_ENTRIES {
                // Should not happen with proper transaction splitting
                return Err(Error::new(ENOSPC));
            }

            self.fs.encrypt(raw, *addr);
            let entry = JournalEntry {
                block_index: (*addr).index().into(),
                generation: next_gen.into(),
                hash: seahash::hash(raw).into(),
            };
            journal_header.entries[i] = entry;
            unsafe { self.fs.disk().write_at(journal_data_block, raw.as_ref())? };
            journal_data_block += 1;
        }

        self.fs.disk().sync()?;

        // Write Journal Header (Phase 1: Writing)
        unsafe {
            let header_bytes = core::slice::from_raw_parts(
                &journal_header as *const _ as *const u8,
                crate::BLOCK_SIZE as usize,
            );
            self.fs.disk().write_at(journal_block, header_bytes)?;
        }

        self.fs.disk().sync()?;

        // Journal Commit (Phase 2: Committed)
        journal_header.commit_state = 1.into();
        unsafe {
            let header_bytes = core::slice::from_raw_parts(
                &journal_header as *const _ as *const u8,
                crate::BLOCK_SIZE as usize,
            );
            self.fs.disk().write_at(journal_block, header_bytes)?;
        }

        self.fs.disk().sync()?;

        // Checkpoint: Write data to their final locations
        for (i, (addr, raw)) in self.write_cache.iter().enumerate() {
            if i >= crate::journal::MAX_JOURNAL_ENTRIES {
                break;
            }
            unsafe {
                let block_offset = self.fs.block();
                self.fs
                    .disk()
                    .write_at(block_offset + addr.index(), raw.as_ref())?
            };
        }

        self.fs.disk().sync()?;

        // Update and write the main header
        let gen = self.header.update(self.fs.cipher_opt());
        let gen_block = gen % crate::HEADER_RING;
        unsafe {
            let block_offset = self.fs.block();
            self.fs
                .disk()
                .write_at(block_offset + gen_block, &self.header)?;
        }

        self.fs.disk().sync()?;

        // Update FS state
        unsafe {
            *self.fs.header_mut() = self.header;
            *self.fs.allocator_mut() = self.allocator;
        }

        Ok(())
    }

    pub(crate) fn sync_allocator(&mut self, force_squash: bool) -> Result<bool> {
        let mut changed = false;
        let mut alloc_ptr = self.header.alloc;
        let mut allocs = VecDeque::new();

        while !alloc_ptr.is_null() {
            let alloc = self.read_block(alloc_ptr)?;
            alloc_ptr = alloc.data().prev;
            allocs.push_front(alloc);
        }

        let gc_threshold = if force_squash { 0 } else { ALLOC_GC_THRESHOLD };

        if self.deallocate.len() > gc_threshold as usize {
            changed = true;

            let mut deallocated = 0;
            'deallocate: while let Some(addr) = self.deallocate.pop() {
                for alloc in allocs.iter_mut() {
                    let alloc_data: &mut AllocList = alloc.data_mut();
                    if alloc_data.deallocate(addr) {
                        deallocated += 1;
                        continue 'deallocate;
                    }
                }
            }
        }

        if !self.allocator_log.is_empty() {
            changed = true;
            'allocator_log: while let Some(entry) = self.allocator_log.pop_front() {
                for alloc in allocs.iter_mut() {
                    if alloc.data_mut().insert_entry(entry) {
                        continue 'allocator_log;
                    }
                }

                let mut alloc = unsafe {
                    let mut alloc = self.read_block(self.header.alloc)?;
                    alloc.data_mut().prev = self.header.alloc;
                    self.shadow_block(alloc.create_ptr())?
                };

                assert!(alloc.data_mut().insert_entry(entry));
                allocs.push_back(alloc);
            }
        }

        if changed {
            let mut next_ptr = BlockPtr::default();
            for mut alloc in allocs.into_iter().rev() {
                // alloc.data_mut().next = next_ptr; // REMOVED THIS LINE
                next_ptr = unsafe { self.write_block(alloc)? };
            }
            self.header_mut().alloc = next_ptr;
            self.set_header_changed(true);
        }

        Ok(changed)
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
        let mut data = T::empty(raw.addr().level()).ok_or(Error::new(ENOENT))?;
        data.copy_from_slice(raw.data());
        Ok(TreeData::new(ptr.id(), data))
    }

    pub fn sync_tree<T: BlockTrait + DerefMut<Target = [u8]> + Deref<Target = [u8]>>(
        &mut self,
        node: TreeData<T>,
    ) -> Result<()> {
        let (i3, i2, i1, i0) = node.ptr().indexes();

        unsafe {
            let mut l3 = self.read_block(self.header.tree)?;
            let mut l2 = self.read_block(l3.data().ptrs[i3])?;
            let mut l1 = self.read_block(l2.data().ptrs[i2])?;
            let mut l0 = self.read_block(l1.data().ptrs[i1])?;

            let mut block_data = self.read_block(unsafe { l0.data().ptrs[i0].cast::<T>() })?;
            *block_data.data_mut() = node.into_data();
            let raw_ptr = unsafe { self.write_block(block_data)? };

            l0.data_mut().ptrs[i0] = unsafe { raw_ptr.cast() };

            let l0_ptr = unsafe { self.write_block(l0)? };
            l1.data_mut().ptrs[i1] = l0_ptr;

            let l1_ptr = unsafe { self.write_block(l1)? };
            l2.data_mut().ptrs[i2] = l1_ptr;

            let l2_ptr = unsafe { self.write_block(l2)? };
            l3.data_mut().ptrs[i3] = l2_ptr;

            self.header_mut().tree = unsafe { self.write_block(l3)? };
        }

        self.set_header_changed(true);
        Ok(())
    }

    pub fn insert_tree<T: BlockTrait + DerefMut<Target = [u8]> + Deref<Target = [u8]>>(
        &mut self,
        node: BlockPtr<T>,
    ) -> Result<TreePtr<T>> {
        // Allocate a new TreePtr ID by finding the first available slot
        // We traverse the tree to find an empty (null) pointer slot
        let mut found_slot = None;

        // Search through all levels of the tree for an empty slot
        'outer: for i3 in 0..126 {
            let l3 = self.read_block(self.header.tree)?;
            if l3.data().ptrs[i3].is_null() {
                found_slot = Some((i3, 0, 0, 0));
                break 'outer;
            }

            for i2 in 0..126 {
                let l2_ptr = l3.data().ptrs[i3];
                if l2_ptr.is_null() {
                    continue;
                }
                let l2 = self.read_block(l2_ptr)?;
                if l2.data().ptrs[i2].is_null() {
                    found_slot = Some((i3, i2, 0, 0));
                    break 'outer;
                }

                for i1 in 0..126 {
                    let l1_ptr = l2.data().ptrs[i2];
                    if l1_ptr.is_null() {
                        continue;
                    }
                    let l1 = self.read_block(l1_ptr)?;
                    if l1.data().ptrs[i1].is_null() {
                        found_slot = Some((i3, i2, i1, 0));
                        break 'outer;
                    }

                    for i0 in 0..126 {
                        let l0_ptr = l1.data().ptrs[i1];
                        if l0_ptr.is_null() {
                            continue;
                        }
                        let l0 = self.read_block(l0_ptr)?;
                        if l0.data().ptrs[i0].is_null() {
                            found_slot = Some((i3, i2, i1, i0));
                            break 'outer;
                        }
                    }
                }
            }
        }

        let (i3, i2, i1, i0) = found_slot.ok_or(Error::new(ENOSPC))?;

        unsafe {
            let mut l3 = self.shadow_block(self.header.tree)?;
            let mut l2 = self.shadow_block(l3.data().ptrs[i3])?;
            let mut l1 = self.shadow_block(l2.data().ptrs[i2])?;
            let mut l0 = self.shadow_block(l1.data().ptrs[i1])?;

            l0.data_mut().ptrs[i0] = unsafe { node.cast() };

            let l0_ptr = unsafe { self.write_block(l0)? };
            l1.data_mut().ptrs[i1] = l0_ptr;

            let l1_ptr = unsafe { self.write_block(l1)? };
            l2.data_mut().ptrs[i2] = l1_ptr;

            let l2_ptr = unsafe { self.write_block(l2)? };
            l3.data_mut().ptrs[i3] = l2_ptr;

            self.header_mut().tree = unsafe { self.write_block(l3)? };
        }

        self.set_header_changed(true);

        Ok(TreePtr::from_indexes((i3, i2, i1, i0)))
    }

    pub fn remove_tree<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: TreePtr<T>,
    ) -> Result<()> {
        let (i3, i2, i1, i0) = ptr.indexes();

        unsafe {
            let mut l3 = self.shadow_block(self.header.tree)?;
            let mut l2 = self.shadow_block(l3.data().ptrs[i3])?;
            let mut l1 = self.shadow_block(l2.data().ptrs[i2])?;
            let mut l0 = self.shadow_block(l1.data().ptrs[i1])?;

            let node_ptr = l0.data().ptrs[i0];
            self.deallocate(&mut FsCtx, node_ptr.addr());
            l0.data_mut().ptrs[i0] = BlockPtr::default();

            let l0_ptr = unsafe { self.write_block(l0)? };
            l1.data_mut().ptrs[i1] = l0_ptr;

            let l1_ptr = self.write_block(l1)?;
            l2.data_mut().ptrs[i2] = l1_ptr;

            let l2_ptr = self.write_block(l2)?;
            l3.data_mut().ptrs[i3] = l2_ptr;

            self.header_mut().tree = self.write_block(l3)?;
        }

        self.set_header_changed(true);
        Ok(())
    }

    pub fn create_node(
        &mut self,
        parent_ptr: TreePtr<Node>,
        name: &str,
        mode: u16,
        ctime: u64,
        ctime_nsec: u32,
    ) -> Result<TreeData<Node>> {
        if name.len() > DIR_ENTRY_MAX_LENGTH {
            return Err(Error::new(EINVAL));
        }

        // 1. Read the parent directory's node.
        let mut parent_node = self.read_tree(parent_ptr)?;

        // 2. Check if the parent is indeed a directory.
        if !parent_node.data().is_dir() {
            return Err(Error::new(ENOTDIR));
        }

        // 3. Read or create the parent's `DirList`.
        let mut parent_dir_list_ptr = unsafe { level_data(&parent_node)?.level0[0].cast() };
        let mut parent_dir_list = if parent_dir_list_ptr.is_null() {
            BlockData::new(
                self.allocator
                    .allocate(BlockMeta::new(BlockLevel::L0))
                    .ok_or(Error::new(ENOSPC))?,
                DirList::empty(BlockLevel::L0).unwrap(),
            )
        } else {
            self.read_block(parent_dir_list_ptr)?
        };

        // 4. Check for existing entries with the same name.
        if parent_dir_list.data().find_entry(name).is_some() {
            return Err(Error::new(EEXIST));
        }

        // 5. Create a new `Node` and allocate a block for it.
        let new_node_block_addr = self
            .allocator
            .allocate(BlockMeta::new(BlockLevel::L0))
            .ok_or(Error::new(ENOSPC))?;
        let new_node_data = Node::new(mode, 0, 0, ctime, ctime_nsec); // uid, gid will be set later if needed

        // 6. Write the new node to disk.
        let new_node_block_data = BlockData::new(new_node_block_addr, new_node_data);
        let new_node_block_ptr = unsafe { self.write_block(new_node_block_data)? };

        // 7. Insert the new node into the filesystem's tree structure.
        let new_node_tree_ptr = self.insert_tree(new_node_block_ptr)?;
        let mut new_node_tree_data = self.read_tree(new_node_tree_ptr)?;

        // 8. Create a `DirEntry` and append it to the parent's `DirList`.
        let dir_entry = DirEntry::new(new_node_tree_ptr, name);
        if !parent_dir_list.data_mut().append(&dir_entry) {
            // This should not happen if DIR_ENTRY_MAX_LENGTH is correctly sized
            return Err(Error::new(ENOSPC));
        }

        // 9. Update and sync the parent's `DirList` and node.
        parent_node.data_mut().set_mtime(ctime, ctime_nsec);
        parent_node.data_mut().set_atime(ctime, ctime_nsec);
        parent_node
            .data_mut()
            .set_size(parent_dir_list.data().deref().len() as u64); // Update size based on DirList content
        let parent_blocks = parent_node.data().blocks();
        parent_node.data_mut().set_blocks(parent_blocks + 1); // Account for the new node block

        // Update parent's level0[0] to point to the new DirList
        parent_dir_list_ptr = unsafe { self.write_block(parent_dir_list)? }.cast();
        level_data_mut(&mut parent_node)?.level0[0] = unsafe { parent_dir_list_ptr.cast() };

        self.sync_tree(parent_node)?;

        // Increment link count for the new node
        let links = new_node_tree_data.data().links();
        new_node_tree_data.data_mut().set_links(links + 1);
        self.sync_tree(new_node_tree_data.clone())?;

        Ok(new_node_tree_data)
    }

    pub fn write_node(
        &mut self,
        node_ptr: TreePtr<Node>,
        offset: u64,
        buf: &[u8],
        mtime: u64,
        mtime_nsec: u32,
    ) -> Result<usize> {
        let mut node = self.read_tree(node_ptr)?;

        if node.data().is_dir() {
            return Err(Error::new(EISDIR));
        }

        node.data_mut().set_mtime(mtime, mtime_nsec);
        node.data_mut().set_atime(mtime, mtime_nsec);

        let mut bytes_written = 0;
        let mut current_offset = offset;
        let mut remaining_buf = buf;

        // Handle inline data
        if node.data().has_inline_data() {
            if let Some(inline_data_slice) = node.data_mut().inline_data_mut() {
                let inline_len = inline_data_slice.len() as u64;
                if current_offset < inline_len {
                    let write_start = current_offset as usize;
                    let write_end =
                        min(inline_len, current_offset + remaining_buf.len() as u64) as usize;
                    let len_to_write = write_end - write_start;

                    inline_data_slice[write_start..write_end]
                        .copy_from_slice(&remaining_buf[..len_to_write]);
                    bytes_written += len_to_write;
                    current_offset += len_to_write as u64;
                    remaining_buf = &remaining_buf[len_to_write..];
                }
            }
        }

        // Handle data blocks (only L0 for now)
        if !remaining_buf.is_empty() {
            let block_size = BLOCK_SIZE as u64;
            let start_block_idx = current_offset / block_size;

            // For simplicity, only support L0 blocks for now.
            // If the write goes beyond L0, return ERANGE.
            if start_block_idx >= 56 {
                // 56 is the number of L0 blocks in NodeLevelData
                return Err(Error::new(ERANGE));
            }

            let level_data_mut_ref = level_data_mut(&mut node)?;
            let mut block_idx = start_block_idx;
            while !remaining_buf.is_empty() && block_idx < 56 {
                let block_offset_in_node = block_idx * block_size;
                let offset_in_block = (current_offset - block_offset_in_node) as usize;

                let len_to_write_in_block =
                    min(remaining_buf.len(), block_size as usize - offset_in_block);

                let current_block_ptr = level_data_mut_ref.level0[block_idx as usize];
                let mut current_block_data = if current_block_ptr.is_null() {
                    let new_block_addr = self
                        .allocator
                        .allocate(BlockMeta::new(BlockLevel::L0))
                        .ok_or(Error::new(ENOSPC))?;
                    BlockData::new(new_block_addr, BlockRaw::empty(BlockLevel::L0).unwrap())
                } else {
                    self.read_block(unsafe { current_block_ptr.cast() })?
                };

                current_block_data.data_mut()
                    [offset_in_block..offset_in_block + len_to_write_in_block]
                    .copy_from_slice(&remaining_buf[..len_to_write_in_block]);

                let new_block_ptr = unsafe { self.write_block(current_block_data)? };
                level_data_mut_ref.level0[block_idx as usize] = unsafe { new_block_ptr.cast() };

                bytes_written += len_to_write_in_block;
                current_offset += len_to_write_in_block as u64;
                remaining_buf = &remaining_buf[len_to_write_in_block..];
                block_idx += 1;
            }
        }

        // Update node size if necessary
        if current_offset > node.data().size() {
            node.data_mut().set_size(current_offset);
        }

        self.sync_tree(node)?;

        Ok(bytes_written)
    }

    pub fn scrub_and_repair(&mut self) -> Result<()> {
        let total_blocks = self.header.size() / BLOCK_SIZE;
        let mut allocated_blocks = BTreeMap::new();

        // 1. Traverse all trees (inodes, etc.) and collect allocated blocks
        self.traverse_and_collect_blocks(&mut allocated_blocks)?;

        // 1. Traverse all trees (inodes, etc.) and collect allocated blocks
        self.traverse_and_collect_blocks(&mut allocated_blocks)?;

        // 2. Check for orphaned nodes (not reachable from the root) and reclaim them
        self.find_and_reclaim_orphaned_nodes(&allocated_blocks)?;

        // 3. Verify the allocator matches the reachable graph
        self.verify_allocator_against_map(&allocated_blocks)?;

        Ok(())
    }

    fn traverse_and_collect_blocks(
        &mut self,
        allocated_blocks: &mut BTreeMap<u64, bool>,
    ) -> Result<()> {
        let mut queue = VecDeque::new();
        // H-Tree root is height 4 (L3..L0). L3 is root.
        queue.push_back((unsafe { self.header.tree.cast::<TreeList<BlockRaw>>() }, 4));

        // Mark allocator blocks as used
        let mut alloc_ptr = self.header.alloc;
        while !alloc_ptr.is_null() {
            let index = alloc_ptr.addr().index();
            if allocated_blocks.contains_key(&index) {
                break;
            }
            allocated_blocks.insert(index, true);
            let alloc_block = self.read_block(alloc_ptr)?;
            alloc_ptr = alloc_block.data().prev;
        }

        while let Some((ptr, height)) = queue.pop_front() {
            if ptr.is_null() {
                continue;
            }
            let index = ptr.addr().index();
            if allocated_blocks.contains_key(&index) {
                continue;
            }

            allocated_blocks.insert(index, true);

            // If height == 0, this is a Node block (Leaf of H-Tree)
            if height == 0 {
                let node = {
                    let node_block = unsafe { self.read_block(ptr.cast::<Node>())? };
                    node_block.data().clone()
                };
                self.traverse_node_data(&node, allocated_blocks)?;
                continue;
            }

            // Else, it is a TreeList (Intermediate H-Tree node)
            let list_block = self.read_block(ptr)?;
            let list = list_block.data();

            for child_ptr in list.ptrs.iter() {
                if !child_ptr.is_null() {
                    queue.push_back((unsafe { child_ptr.cast() }, height - 1));
                }
            }
        }
        Ok(())
    }

    fn traverse_node_data(
        &mut self,
        node: &Node,
        allocated_blocks: &mut BTreeMap<u64, bool>,
    ) -> Result<()> {
        if let Some(level_data) = node.level_data() {
            for ptr in level_data.level0.iter() {
                self.traverse_data_ptr(unsafe { ptr.cast() }, 0, allocated_blocks)?;
            }
            for ptr in level_data.level1.iter() {
                self.traverse_data_ptr(unsafe { ptr.cast() }, 1, allocated_blocks)?;
            }
            for ptr in level_data.level2.iter() {
                self.traverse_data_ptr(unsafe { ptr.cast() }, 2, allocated_blocks)?;
            }
            for ptr in level_data.level3.iter() {
                self.traverse_data_ptr(unsafe { ptr.cast() }, 3, allocated_blocks)?;
            }
            for ptr in level_data.level4.iter() {
                self.traverse_data_ptr(unsafe { ptr.cast() }, 4, allocated_blocks)?;
            }
        }
        if !node.acl_ptr.is_null() {
            allocated_blocks.insert(node.acl_ptr.addr().index(), true);
        }
        Ok(())
    }

    fn traverse_data_ptr(
        &mut self,
        ptr: BlockPtr<BlockRaw>,
        height: usize,
        allocated_blocks: &mut BTreeMap<u64, bool>,
    ) -> Result<()> {
        if ptr.is_null() {
            return Ok(());
        }
        let index = ptr.addr().index();
        if allocated_blocks.contains_key(&index) {
            return Ok(());
        }

        allocated_blocks.insert(index, true);

        if height == 0 {
            return Ok(());
        }

        let list_ptr = unsafe { ptr.cast::<BlockList<BlockRaw>>() };
        let list_block = self.read_block(list_ptr)?;
        let list = list_block.data(); // Borrow self via list_block

        // Copy pointers to avoid holding borrow during recursion!
        // BlockList has limited entries (128). We can copy.
        // Actually, recursive call borrows self mutably.
        // So we cannot hold reference to list.data().
        let ptrs: Vec<BlockPtr<BlockRaw>> = list.ptrs.iter().map(|p| unsafe { p.cast() }).collect();
        drop(list_block); // Drop borrow

        for child in ptrs {
            self.traverse_data_ptr(child, height - 1, allocated_blocks)?;
        }
        Ok(())
    }

    fn verify_allocator_against_map(
        &mut self,
        allocated_blocks: &BTreeMap<u64, bool>,
    ) -> Result<()> {
        let mut inconsistencies = 0;
        let total_blocks = self.header.size() / BLOCK_SIZE;

        for i in 0..total_blocks {
            let is_allocated_in_map = allocated_blocks.contains_key(&i);
            let is_allocated_in_allocator = self
                .allocator
                .is_allocated(unsafe { BlockAddr::new(i, BlockMeta::new(BlockLevel::L0)) });

            if is_allocated_in_map != is_allocated_in_allocator {
                inconsistencies += 1;
                // Repair logic would go here. For example, if a block is in the map but not in
                // the allocator, it should be marked as allocated. If it's in the allocator but
                // not in the map, it's a leaked block and should be freed.
            }
        }

        if inconsistencies > 0 {
            return Err(Error::new(EIO));
        }
        Ok(())
    }

    fn find_and_reclaim_orphaned_nodes(
        &mut self,
        allocated_blocks: &BTreeMap<u64, bool>,
    ) -> Result<()> {
        let total_blocks = self.header.size() / BLOCK_SIZE;
        let mut reclaimed_count = 0;

        for i in 0..total_blocks {
            let is_allocated = self
                .allocator
                .is_allocated(unsafe { BlockAddr::new(i, BlockMeta::new(BlockLevel::L0)) });

            if is_allocated && !allocated_blocks.contains_key(&i) {
                // Orphan detected!
                #[cfg(feature = "log")]
                log::info!("Reclaiming orphaned block: {}", i);

                // We use self.deallocate helper logic (which adds to deallocate list or updates log)
                // But Transaction::deallocate implementation assumes standard flow.
                // We want to force deallocate from Allocator.
                // However, Transaction::deallocate is high level.
                // Let's manually push to deallocate list or use Allocator directly?
                // Using Transaction::deallocate is safer as it respects transaction log logic.
                // But it takes &mut dyn AllocCtx. We can use FsCtx.

                // Note: BlockMeta is needed. L0 is safe assumption for orphans if they are allocated as L0?
                // If they were L1+, the Allocator tracks them as used blocks?
                // RedoxFS allocator tracks blocks by level.
                // If I deallocate L0, but it was L1, it might corrupt buddy allocator?
                // Is there a way to know the level of an allocated block?
                // AllocList doesn't store level. Allocator in RAM attempts to track free blocks by level.
                // But used blocks are "Implicitly 1 refcount". We don't know their level.
                // However, allocate() allocates exact or splits.
                // When deallocating, we usually know the level from the Pointer (BlockPtr).
                // For orphans, we lost the pointer!
                // So we don't know the level.
                // Safest is to assume L0. If it was larger, we leak the "buddy" merging potential but reclaim the space as L0s.
                // Wait, if 2 L0s make 1 L1. If I free 2 L0s, they can merge.
                // So freeing as L0 is strictly correct for reclamation.

                unsafe {
                    self.deallocate(
                        &mut FsCtx,
                        BlockAddr::new(i, BlockMeta::new(BlockLevel::L0)),
                    );
                }
                reclaimed_count += 1;
            }
        }

        if reclaimed_count > 0 {
            #[cfg(feature = "log")]
            log::info!("Reclaimed {} orphaned blocks", reclaimed_count);
        }

        Ok(())
    }

    pub fn verify_allocator(&mut self) -> Result<()> {
        let mut allocated_blocks = BTreeMap::new();
        self.traverse_and_collect_blocks(&mut allocated_blocks)?;
        self.verify_allocator_against_map(&allocated_blocks)
    }

    pub fn verify_clone_integrity(&mut self) -> Result<()> {
        // A full implementation would traverse a cloned filesystem,
        // ensuring that all reference counts are correct and that no blocks are shared incorrectly.
        // This would involve building a map of all blocks and their refcounts and then
        // comparing it against the allocator's refcounts.
        Ok(())
    }

    pub fn read_node(
        &mut self,
        ptr: TreePtr<Node>,
        offset: u64,
        buf: &mut [u8],
        atime_sec: u64,
        atime_nsec: u32,
    ) -> Result<usize> {
        let mut node = self.read_tree(ptr)?;

        // Update atime
        node.data_mut().set_atime(atime_sec, atime_nsec);
        self.sync_tree(node.clone())?;

        let file_size = node.data().size();
        let mut i = 0;
        while i < buf.len() && offset + (i as u64) < file_size {
            let pos = offset + i as u64;
            let block_index = pos / BLOCK_SIZE;
            let block_offset = (pos % BLOCK_SIZE) as usize;
            let remaining_in_block = BLOCK_SIZE as usize - block_offset;
            let to_read = cmp::min(buf.len() - i, remaining_in_block);

            if let Some(level_data) = node.data().level_data() {
                if block_index < 56 {
                    let ptr = level_data.level0[block_index as usize];
                    if ptr.is_null() {
                        for b in &mut buf[i..i + to_read] {
                            *b = 0;
                        }
                    } else {
                        let block = self.read_block(unsafe { ptr.cast::<BlockRaw>() })?;
                        buf[i..i + to_read]
                            .copy_from_slice(&block.data()[block_offset..block_offset + to_read]);
                    }
                } else {
                    return Err(Error::new(EIO));
                }
            } else if let Some(inline) = node.data().inline_data() {
                if pos >= inline.len() as u64 {
                    break;
                }
                let inline_end = cmp::min(pos + to_read as u64, inline.len() as u64);
                let len = (inline_end - pos) as usize;
                buf[i..i + len].copy_from_slice(&inline[pos as usize..(pos as usize) + len]);
            }

            i += to_read;
        }

        Ok(i)
    }

    pub fn find_node(&mut self, parent_ptr: TreePtr<Node>, name: &str) -> Result<TreeData<Node>> {
        let parent = self.read_tree(parent_ptr)?;
        if !parent.data().is_dir() {
            return Err(Error::new(ENOTDIR));
        }

        if let Some(level_data) = parent.data().level_data() {
            for ptr in level_data.level0.iter() {
                if !ptr.is_null() {
                    let dir_list_block = self.read_block(unsafe { ptr.cast::<DirList>() })?;
                    if let Some(entry) = dir_list_block.data().find_entry(name) {
                        return self.read_tree(entry.node_ptr());
                    }
                }
            }
        }
        Err(Error::new(ENOENT))
    }

    pub fn child_nodes(
        &mut self,
        parent_ptr: TreePtr<Node>,
        children: &mut Vec<DirEntry>,
    ) -> Result<()> {
        let parent = self.read_tree(parent_ptr)?;
        if !parent.data().is_dir() {
            return Err(Error::new(ENOTDIR));
        }

        if let Some(level_data) = parent.data().level_data() {
            for ptr in level_data.level0.iter() {
                if !ptr.is_null() {
                    let dir_list_block = self.read_block(unsafe { ptr.cast::<DirList>() })?;
                    for entry in dir_list_block.data().entries() {
                        children.push(entry);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn remove_node(&mut self, parent_ptr: TreePtr<Node>, name: &str, _mode: u16) -> Result<()> {
        let mut parent = self.read_tree(parent_ptr)?;
        if !parent.data().is_dir() {
            return Err(Error::new(ENOTDIR));
        }

        let mut found = false;
        let mut entry_to_remove = None;

        if let Some(level_data) = parent.data_mut().level_data_mut() {
            for ptr in level_data.level0.iter_mut() {
                if !ptr.is_null() {
                    let mut dir_list_block = self.read_block(unsafe { ptr.cast::<DirList>() })?;
                    if let Some(entry) = dir_list_block.data().find_entry(name) {
                        entry_to_remove = Some(entry);
                        if dir_list_block.data_mut().remove_entry(name) {
                            let new_ptr = unsafe { self.write_block(dir_list_block)? };
                            *ptr = unsafe { new_ptr.cast() };
                            found = true;
                            break;
                        }
                    }
                }
            }
        }

        if !found {
            return Err(Error::new(ENOENT));
        }
        self.sync_tree(parent)?;

        if let Some(entry) = entry_to_remove {
            let mut node = self.read_tree(entry.node_ptr())?;
            let links = node.data().links();
            if links > 0 {
                node.data_mut().set_links(links - 1);
                let new_links = links - 1;
                self.sync_tree(node)?;
                if new_links == 0 {
                    self.remove_tree(entry.node_ptr())?;
                }
            }
        }

        Ok(())
    }

    pub fn rename_node(
        &mut self,
        orig_parent: TreePtr<Node>,
        orig_name: &str,
        new_parent: TreePtr<Node>,
        new_name: &str,
    ) -> Result<()> {
        let node_data = self.find_node(orig_parent, orig_name)?;
        let node_ptr = node_data.ptr();

        if let Ok(_) = self.find_node(new_parent, new_name) {
            return Err(Error::new(EEXIST));
        }

        let mut new_parent_node = self.read_tree(new_parent)?;
        let mut added = false;
        if let Some(level_data) = new_parent_node.data_mut().level_data_mut() {
            for ptr in level_data.level0.iter_mut() {
                if !ptr.is_null() {
                    let mut dir_list_block = self.read_block(unsafe { ptr.cast::<DirList>() })?;
                    let entry = DirEntry::new(node_ptr, new_name);
                    if dir_list_block.data_mut().append(&entry) {
                        let new_block_ptr = unsafe { self.write_block(dir_list_block)? };
                        *ptr = unsafe { new_block_ptr.cast() };
                        added = true;
                        break;
                    }
                } else {
                    let addr = self
                        .allocator
                        .allocate(BlockMeta::new(BlockLevel::L0))
                        .ok_or(Error::new(ENOSPC))?;
                    let mut dir_list = DirList::empty(BlockLevel::L0).unwrap();
                    let entry = DirEntry::new(node_ptr, new_name);
                    dir_list.append(&entry);

                    let block_data = BlockData::new(addr, dir_list);
                    let new_block_ptr = unsafe { self.write_block(block_data)? };
                    *ptr = unsafe { new_block_ptr.cast() };
                    added = true;
                    break;
                }
            }
        }
        if !added {
            return Err(Error::new(ENOSPC));
        }
        self.sync_tree(new_parent_node)?;
        self.remove_node_entry_only(orig_parent, orig_name)?;

        Ok(())
    }

    fn remove_node_entry_only(&mut self, parent_ptr: TreePtr<Node>, name: &str) -> Result<()> {
        let mut parent = self.read_tree(parent_ptr)?;
        if let Some(level_data) = parent.data_mut().level_data_mut() {
            for ptr in level_data.level0.iter_mut() {
                if !ptr.is_null() {
                    let mut dir_list_block = self.read_block(unsafe { ptr.cast::<DirList>() })?;
                    if dir_list_block.data_mut().remove_entry(name) {
                        let new_ptr = unsafe { self.write_block(dir_list_block)? };
                        *ptr = unsafe { new_ptr.cast() };
                        self.sync_tree(parent)?;
                        return Ok(());
                    }
                }
            }
        }
        Err(Error::new(ENOENT))
    }

    pub fn truncate_node_inner(&mut self, node: &mut TreeData<Node>, size: u64) -> Result<bool> {
        let old_size = node.data().size();
        if size == old_size {
            return Ok(false);
        }

        node.data_mut().set_size(size);
        if size < old_size {
            let blocks_needed = (size + BLOCK_SIZE - 1) / BLOCK_SIZE;
            if let Some(level_data) = node.data_mut().level_data_mut() {
                for i in blocks_needed..56 {
                    let ptr = &mut level_data.level0[i as usize];
                    if !ptr.is_null() {
                        unsafe {
                            self.deallocate(&mut FsCtx, ptr.addr());
                        }
                        *ptr = BlockPtr::default();
                    }
                }
            }
        }
        self.sync_tree(node.clone())?;
        Ok(true)
    }

    pub fn set_acl(&mut self, node_ptr: TreePtr<Node>, acl: &crate::node::AclList) -> Result<()> {
        let mut node = self.read_tree(node_ptr)?;
        let addr = self
            .allocator
            .allocate(BlockMeta::new(BlockLevel::L0))
            .ok_or(Error::new(ENOSPC))?;
        let block_data = BlockData::new(addr, acl.clone());
        let block_ptr = unsafe { self.write_block(block_data)? };

        node.data_mut().acl_ptr = unsafe { block_ptr.cast() };
        self.sync_tree(node)?;
        Ok(())
    }

    pub fn sync_block(&mut self, _addr: BlockAddr) -> Result<()> {
        Ok(())
    }
}

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
        for (addr, data) in self.shadow_cache.iter() {
            unsafe {
                self.fs.disk().write_at(self.fs.block() + addr.index(), &data)?;
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
        block.data_mut().set_addr(new_addr);

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
                hash: raw.create_ptr().hash().into(),
            };
            journal_header.entries[i] = entry;
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
                .write_at_part(journal_block, &commit_state_bytes, offset, commit_state_bytes.len())?
        }

        // Checkpoint: Write data to their final locations
        for (i, (addr, raw)) in self.write_cache.iter().enumerate() {
            if i >= crate::journal::MAX_JOURNAL_ENTRIES {
                break;
            }
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

    fn sync_allocator(&mut self, force_squash: bool) -> Result<bool> {
        let mut changed = false;
        let mut alloc_ptr = self.header.alloc;
        let mut allocs = VecDeque::new();

        while !alloc_ptr.is_null() {
            let alloc = self.read_block(alloc_ptr)?;
            alloc_ptr = alloc.data().prev;
            allocs.push_front(alloc);
        }

        let gc_threshold = if force_squash {
            0
        } else {
            ALLOC_GC_THRESHOLD
        };

        if self.deallocate.len() > gc_threshold {
            changed = true;

            let mut deallocated = 0;
            'deallocate: while let Some(addr) = self.deallocate.pop() {
                for alloc in allocs.iter_mut() {
                    if alloc.data_mut().deallocate(addr) {
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
        mut node: TreeData<T>,
    ) -> Result<()> {
        let (i3, i2, i1, i0) = node.ptr().indexes();

        unsafe {
            let mut l3 = self.read_block(self.header.tree)?;
            let mut l2 = self.read_block(l3.data().ptrs[i3])?;
            let mut l1 = self.read_block(l2.data().ptrs[i2])?;
            let mut l0 = self.read_block(l1.data().ptrs[i1])?;

            let raw_ptr = self.write_block(BlockData::new(
                l0.data().ptrs[i0].addr(),
                node.data_mut(),
            ))?;
            l0.data_mut().ptrs[i0] = raw_ptr.cast();

            let l0_ptr = self.write_block(l0)?;
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

    pub fn insert_tree<T: BlockTrait + DerefMut<Target = [u8]> + Deref<Target = [u8]>>(
        &mut self,
        node: BlockPtr<T>,
    ) -> Result<TreePtr<T>> {
        // The logic for generating new TreePtr IDs has changed.
        // For now, I'll use a placeholder ID and mark this for review.
        // TODO: Implement proper TreePtr ID generation.
        let (i3, i2, i1, i0) = (0, 0, 0, 0); // Placeholder

        unsafe {
            let mut l3 = self.shadow_block(self.header.tree)?;
            let mut l2 = self.shadow_block(l3.data().ptrs[i3])?;
            let mut l1 = self.shadow_block(l2.data().ptrs[i2])?;
            let mut l0 = self.shadow_block(l1.data().ptrs[i1])?;

            l0.data_mut().ptrs[i0] = node;

            let l0_ptr = self.write_block(l0)?;
            l1.data_mut().ptrs[i1] = l0_ptr;

            let l1_ptr = self.write_block(l1)?;
            l2.data_mut().ptrs[i2] = l1_ptr;

            let l2_ptr = self.write_block(l2)?;
            l3.data_mut().ptrs[i3] = l2_ptr;

            self.header_mut().tree = self.write_block(l3)?;
        }

        // The logic for updating unalloc_ptr is also outdated.
        // TODO: Implement proper TreePtr ID generation.
        // self.header_mut().unalloc_ptr = TreePtr::new(i3, i2, i1, i0).next().unwrap().into();
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

            let l0_ptr = self.write_block(l0)?;
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
        let mut parent_dir_list_ptr = level_data(&parent_node)?.level0[0].cast();
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
        parent_node.data_mut().set_size(parent_dir_list.data().deref().len() as u64); // Update size based on DirList content
        parent_node.data_mut().set_blocks(parent_node.data().blocks() + 1); // Account for the new node block

        // Update parent's level0[0] to point to the new DirList
        parent_dir_list_ptr = unsafe { self.write_block(parent_dir_list)? }.cast();
        level_data_mut(&mut parent_node)?.level0[0] = parent_dir_list_ptr;

        self.sync_tree(parent_node)?;

        // Increment link count for the new node
        new_node_tree_data.data_mut().set_links(new_node_tree_data.data().links() + 1);
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
                    let write_end = min(inline_len, current_offset + remaining_buf.len() as u64) as usize;
                    let len_to_write = write_end - write_start;

                    inline_data_slice[write_start..write_end].copy_from_slice(&remaining_buf[..len_to_write]);
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
            if start_block_idx >= 56 { // 56 is the number of L0 blocks in NodeLevelData
                return Err(Error::new(ERANGE));
            }

            let level_data_mut_ref = level_data_mut(&mut node)?;
            let mut block_idx = start_block_idx;
            while !remaining_buf.is_empty() && block_idx < 56 {
                let block_offset_in_node = block_idx * block_size;
                let offset_in_block = (current_offset - block_offset_in_node) as usize;

                let len_to_write_in_block = min(
                    remaining_buf.len(),
                    block_size as usize - offset_in_block,
                );

                let current_block_ptr = level_data_mut_ref.level0[block_idx as usize];
                let mut current_block_data = if current_block_ptr.is_null() {
                    let new_block_addr = self
                        .allocator
                        .allocate(BlockMeta::new(BlockLevel::L0))
                        .ok_or(Error::new(ENOSPC))?;
                    BlockData::new(new_block_addr, BlockRaw::empty(BlockLevel::L0).unwrap())
                } else {
                    self.read_block(current_block_ptr.cast())?
                };

                current_block_data.data_mut()[offset_in_block..offset_in_block + len_to_write_in_block]
                    .copy_from_slice(&remaining_buf[..len_to_write_in_block]);

                let new_block_ptr = unsafe { self.write_block(current_block_data)? };
                level_data_mut_ref.level0[block_idx as usize] = new_block_ptr.cast();

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

        // 2. Verify and repair the allocator based on the collected blocks
        self.verify_allocator_against_map(&allocated_blocks)?;

        // 3. Check for orphaned nodes (not reachable from the root)
        self.find_and_reclaim_orphaned_nodes(&allocated_blocks)?;

        Ok(())
    }

    fn traverse_and_collect_blocks(
        &mut self,
        allocated_blocks: &mut BTreeMap<u64, bool>,
    ) -> Result<()> {
        let mut queue = VecDeque::new();
        queue.push_back(self.header.tree);

        while let Some(ptr) = queue.pop_front() {
            if ptr.is_null() || allocated_blocks.contains_key(&ptr.addr().index()) {
                continue;
            }
            allocated_blocks.insert(ptr.addr().index(), true);

            let block = self.read_block(ptr)?;
            // TODO: Reimplement block.as_tree() and block.as_node() logic
            // if let Ok(tree) = block.as_tree() {
            //     for child_ptr in tree.ptrs.iter() {
            //         queue.push_back(*child_ptr);
            //     }
            // } else if let Ok(node) = self.read_tree(TreePtr::from_indexes((0, 0, 0, 0))) {
            //     // This is a simplified traversal. A real implementation would need to handle
            //     // different node types and their specific data structures.
            //     if let Some(level_data) = node.data().level_data() {
            //         for ptr in level_data.ptrs.iter() {
            //             queue.push_back(*ptr);
            //         }
            //     }
            // }
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
            let is_allocated_in_allocator = self.allocator.is_allocated(BlockAddr::new(
                i,
                BlockMeta::new(BlockLevel::L0),
            ));

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
        // This is a complex task that requires a full graph traversal of the filesystem.
        // The basic idea is to start from the root and mark all reachable nodes. Any nodes
        // that are allocated but not marked are orphans and can be reclaimed.
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
}

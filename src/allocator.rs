use alloc::{collections::{BTreeMap, BTreeSet}, vec::Vec};
use core::{fmt, mem, ops, slice};
use endian_num::Le;

use crate::{BlockAddr, BlockLevel, BlockMeta, BlockPtr, BlockTrait, BLOCK_SIZE};

pub const ALLOC_LIST_ENTRIES: usize =
    (BLOCK_SIZE as usize - mem::size_of::<BlockPtr<AllocList>>()) / mem::size_of::<AllocEntry>();

/// The RedoxFS block allocator. This struct manages all "data" blocks in RedoxFS.
#[derive(Clone, Default)]
pub struct Allocator {
    /// Keeps track of free blocks by level.
    levels: Vec<BTreeSet<u64>>,
    /// Maps block index to reference count.
    /// If a block is not in this map but is not free, its refcount is implicitly 1.
    /// If a block is free, it should not be in this map.
    refcounts: BTreeMap<u64, u64>,
}

impl Allocator {
    pub fn levels(&self) -> &Vec<BTreeSet<u64>> {
        &self.levels
    }

    /// Count the number of free [`BLOCK_SIZE`] available to this [`Allocator`].
    pub fn free(&self) -> u64 {
        let mut free = 0;
        for level in 0..self.levels.len() {
            let level_size = 1 << level;
            free += self.levels[level].len() as u64 * level_size;
        }
        free
    }

    /// Increment the reference count of a block.
    pub fn increment_refcount(&mut self, addr: BlockAddr) {
        let index = addr.index();
        let count = self.refcounts.entry(index).or_insert(1);
        *count += 1;
    }

    /// Decrement the reference count of a block.
    /// Returns the new refcount.
    pub fn decrement_refcount(&mut self, addr: BlockAddr) -> u64 {
        let index = addr.index();
        // If not in map, implicitly 1. Decrementing goes to 0.
        // If in map, decrement. If 0, remove.
        if let Some(count) = self.refcounts.get_mut(&index) {
            if *count > 1 {
                *count -= 1;
                return *count;
            } else {
                self.refcounts.remove(&index);
                return 0;
            }
        }
        // Implicit 1 -> 0
        0
    }

    /// Find a free block of the given level, mark it as "used", and return its address.
    pub fn allocate(&mut self, meta: BlockMeta) -> Option<BlockAddr> {
        // Helper to find a free block
        let find_free = |alloc: &Allocator| -> Option<(usize, u64)> {
            let mut best_opt: Option<(usize, u64)> = None;
            let mut level = meta.level.0;
            while level < alloc.levels.len() {
                if let Some(&index) = alloc.levels[level].first() {
                    best_opt = match best_opt {
                        Some((best_level, best_index)) if best_index <= index => {
                            Some((best_level, best_index))
                        }
                        _ => Some((level, index)),
                    };
                }
                level += 1;
            }
            best_opt
        };

        // First attempt
        let mut free_opt = find_free(self);

        // If failed, try coalescing
        if free_opt.is_none() {
            self.coalesce();
            free_opt = find_free(self);
        }

        // If a free block was found, split it until we find a usable block of the right level.
        let (mut level, index) = free_opt?;
        self.levels[level].remove(&index);
        while level > meta.level.0 {
            level -= 1;
            let level_size = 1 << level;
            self.levels[level].insert(index + level_size);
        }

        let addr = unsafe { BlockAddr::new(index, meta) };
        // Start with refcount 1 (implicit, or explicit if we want to be verbose, but implicit saves memory)
        // self.refcounts.insert(index, 1);
        Some(addr)
    }

    /// Coalesce free blocks to form larger blocks.
    pub fn coalesce(&mut self) {
        let mut level = 0;
        while level < self.levels.len() {
            let level_size = 1 << level;
            let next_size = level_size << 1;

            let mut removals = Vec::new();
            let mut inserts = Vec::new();

            let blocks: Vec<u64> = self.levels[level].iter().cloned().collect();

            let mut i = 0;
            while i < blocks.len() {
                let index = blocks[i];
                if index % next_size == 0 {
                    let buddy = index + level_size;
                    if i + 1 < blocks.len() && blocks[i+1] == buddy {
                        removals.push(index);
                        removals.push(buddy);
                        inserts.push(index);
                        i += 2;
                        continue;
                    }
                }
                i += 1;
            }

            if removals.is_empty() {
                level += 1;
                continue;
            }

            for index in removals {
                self.levels[level].remove(&index);
            }

            if level + 1 >= self.levels.len() {
                self.levels.push(BTreeSet::new());
            }

            for index in inserts {
                self.levels[level + 1].insert(index);
            }

            level += 1;
        }
    }

    pub fn allocate_exact(&mut self, exact_addr: BlockAddr) -> Option<BlockAddr> {
        assert_eq!(exact_addr.level().0, 0);
        let exact_index = exact_addr.index();

        let mut index_opt = None;

        for level in (0..self.levels.len()).rev() {
            let level_size = 1 << level;

            if let Some(index) = index_opt.take() {
                self.levels[level].insert(index);
                self.levels[level].insert(index + level_size);
            }

            for &start in self.levels[level].iter() {
                if start <= exact_index {
                    let end = start + level_size;
                    if end > exact_index {
                        self.levels[level].remove(&start);
                        index_opt = Some(start);
                        break;
                    }
                }
            }
        }

        Some(unsafe { BlockAddr::new(index_opt?, exact_addr.meta()) })
    }

    /// Deallocate the given block.
    /// Only actually returns the block to the free list if the refcount reaches 0.
    pub fn deallocate(&mut self, addr: BlockAddr) {
        let mut index = addr.index();
        let mut level = addr.level().0;

        // Lazy coalescing
        if level <= 2 {
            while level >= self.levels.len() {
                self.levels.push(BTreeSet::new());
            }
            self.levels[level].insert(index);
            return;
        }

        loop {
            while level >= self.levels.len() {
                self.levels.push(BTreeSet::new());
            }

            let level_size = 1 << level;
            let next_size = level_size << 1;

            let mut found = false;
            for &level_index in self.levels[level].iter() {
                if index % next_size == 0 && index + level_size == level_index {
                    self.levels[level].remove(&level_index);
                    found = true;
                    break;
                } else if level_index % next_size == 0 && level_index + level_size == index {
                    self.levels[level].remove(&level_index);
                    index = level_index;
                    found = true;
                    break;
                }
            }

            if !found {
                self.levels[level].insert(index);
                return;
            }

            level += 1;
        }
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy, Default, Debug)]
pub struct AllocEntry {
    index: Le<u64>,
    count: Le<i64>,
}

impl AllocEntry {
    pub fn new(index: u64, count: i64) -> Self {
        Self {
            index: index.into(),
            count: count.into(),
        }
    }

    pub fn allocate(addr: BlockAddr) -> Self {
        Self::new(addr.index(), -addr.level().blocks::<i64>())
    }

    pub fn deallocate(addr: BlockAddr) -> Self {
        Self::new(addr.index(), addr.level().blocks::<i64>())
    }

    pub fn index(&self) -> u64 {
        self.index.to_ne()
    }

    pub fn count(&self) -> i64 {
        self.count.to_ne()
    }

    pub fn is_null(&self) -> bool {
        self.count() == 0
    }
}

#[repr(C, packed)]
pub struct AllocList {
    pub prev: BlockPtr<AllocList>,
    pub entries: [AllocEntry; ALLOC_LIST_ENTRIES],
}

unsafe impl BlockTrait for AllocList {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self {
                prev: BlockPtr::default(),
                entries: [AllocEntry::default(); ALLOC_LIST_ENTRIES],
            })
        } else {
            None
        }
    }
}

impl fmt::Debug for AllocList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prev = self.prev;
        let entries: Vec<&AllocEntry> = self
            .entries
            .iter()
            .filter(|entry| entry.count() > 0)
            .collect();
        f.debug_struct("AllocList")
            .field("prev", &prev)
            .field("entries", &entries)
            .finish()
    }
}

impl ops::Deref for AllocList {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self as *const AllocList as *const u8,
                mem::size_of::<AllocList>(),
            ) as &[u8]
        }
    }
}

impl ops::DerefMut for AllocList {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(
                self as *mut AllocList as *mut u8,
                mem::size_of::<AllocList>(),
            ) as &mut [u8]
        }
    }
}

#[test]
fn alloc_node_size_test() {
    assert_eq!(mem::size_of::<AllocList>(), crate::BLOCK_SIZE as usize);
}
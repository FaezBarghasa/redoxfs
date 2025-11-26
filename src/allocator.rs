use alloc::{collections::BTreeSet, vec::Vec};
use core::{fmt, mem, ops, slice};
use endian_num::Le;

use crate::{BlockAddr, BlockLevel, BlockMeta, BlockPtr, BlockTrait, BLOCK_SIZE};

pub const ALLOC_LIST_ENTRIES: usize =
    (BLOCK_SIZE as usize - mem::size_of::<BlockPtr<AllocList>>()) / mem::size_of::<AllocEntry>();

/// The RedoxFS block allocator. This struct manages all "data" blocks in RedoxFS
/// (i.e, all blocks that aren't reserved or part of the header chain).
///
/// [`Allocator`] can allocate blocks of many "levels"---that is, it can
/// allocate multiple consecutive [`BLOCK_SIZE`] blocks in one operation.
///
/// This reduces the amount of memory that the [`Allocator`] uses:
/// Instead of storing the index of each free [`BLOCK_SIZE`] block,
/// the `levels` array can keep track of higher-level blocks, splitting
/// them when a smaller block is requested.
///
/// Higher-level blocks also allow us to more efficiently allocate memory
/// for large files.
#[derive(Clone, Default)]
pub struct Allocator {
    /// This array keeps track of all free blocks of each level,
    /// and is initialized using the AllocList chain when we open the filesystem.
    ///
    /// Every element of the outer array represents a block level:
    /// - item 0: free level 0 blocks (with size [`BLOCK_SIZE`])
    /// - item 1: free level 1 blocks (with size 2*[`BLOCK_SIZE`])
    /// - item 2: free level 2 blocks (with size 4*[`BLOCK_SIZE`])
    /// ...and so on.
    ///
    /// Each inner array contains a list of free block indices,
    levels: Vec<BTreeSet<u64>>,
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

    /// Find a free block of the given level, mark it as "used", and return its address.
    /// Returns [`None`] if there are no free blocks with this level.
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
        // The left side of the split block is kept free, and the right side is allocated.
        let (mut level, index) = free_opt?;
        self.levels[level].remove(&index);
        while level > meta.level.0 {
            level -= 1;
            let level_size = 1 << level;
            self.levels[level].insert(index + level_size);
        }

        Some(unsafe { BlockAddr::new(index, meta) })
    }

    /// Coalesce free blocks to form larger blocks.
    /// This is used when allocation fails to find a block of sufficient size.
    pub fn coalesce(&mut self) {
        let mut level = 0;
        while level < self.levels.len() {
            let level_size = 1 << level;
            let next_size = level_size << 1;
            
            let mut removals = Vec::new();
            let mut inserts = Vec::new();
            
            // Iterate over blocks and find buddies
            // Since BTreeSet is sorted, we can look for index and index+size
            let blocks: Vec<u64> = self.levels[level].iter().cloned().collect();
            
            let mut i = 0;
            while i < blocks.len() {
                let index = blocks[i];
                // Check alignment for left buddy
                if index % next_size == 0 {
                    // Look for right buddy
                    let buddy = index + level_size;
                    // Check if next block in list is buddy
                    if i + 1 < blocks.len() && blocks[i+1] == buddy {
                        // Found pair
                        removals.push(index);
                        removals.push(buddy);
                        inserts.push(index); // Add to next level
                        i += 2; // Skip both
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
            
            // Ensure next level exists
            if level + 1 >= self.levels.len() {
                self.levels.push(BTreeSet::new());
            }
            
            for index in inserts {
                self.levels[level + 1].insert(index);
            }
            
            // Don't increment level immediately, re-scan this level? 
            // No, we moved blocks to level+1. We should scan level+1 next.
            // But we might have created new opportunities in level+1.
            // So incrementing level is correct.
            level += 1;
        }
    }

    /// Try to allocate the exact block specified, making all necessary splits.
    /// Returns [`None`] if this some (or all) of this block is already allocated.
    ///
    /// Note that [`BlockAddr`] encodes the blocks location _and_ level.
    pub fn allocate_exact(&mut self, exact_addr: BlockAddr) -> Option<BlockAddr> {
        // This function only supports level 0 right now
        assert_eq!(exact_addr.level().0, 0);
        let exact_index = exact_addr.index();

        let mut index_opt = None;

        // Go from the highest to the lowest level
        for level in (0..self.levels.len()).rev() {
            let level_size = 1 << level;

            // Split higher block if found
            if let Some(index) = index_opt.take() {
                self.levels[level].insert(index);
                self.levels[level].insert(index + level_size);
            }

            // Look for matching block and remove it
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

    /// Deallocate the given block, marking it "free" so that it can be re-used later.
    pub fn deallocate(&mut self, addr: BlockAddr) {
        // When we deallocate, we check if block we're deallocating has a free sibling.
        // If it does, we join the two to create one free block in the next (higher) level.
        //
        // We repeat this until we no longer have a sibling to join.
        let mut index = addr.index();
        let mut level = addr.level().0;

        // Lazy coalescing: For small blocks (Level 0-2), skip the aggressive "buddy" coalescing loop
        // during high-frequency operations. Add them directly to the free list.
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
            // look at all free blocks in the current level...
            for &level_index in self.levels[level].iter() {
                // - the block we just freed aligns with the next largest block, and
                // - the second block we're looking at is the right sibling of this block
                if index % next_size == 0 && index + level_size == level_index {
                    // "alloc" the next highest block, repeat deallocation process.
                    self.levels[level].remove(&level_index);
                    found = true;
                    break;
                // - the index of this block doesn't align with the next largest block, and
                // - the block we're looking at is the left neighbor of this block
                } else if level_index % next_size == 0 && level_index + level_size == index {
                    // "alloc" the next highest block, repeat deallocation process.
                    self.levels[level].remove(&level_index);
                    index = level_index; // index moves to left block
                    found = true;
                    break;
                }
            }

            // We couldn't find a higher block,
            // deallocate this one and finish
            if !found {
                self.levels[level].insert(index);
                return;
            }

            // repeat deallocation process on the
            // higher-level block we just created.
            level += 1;
        }
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy, Default, Debug)]
pub struct AllocEntry {
    /// The index of the first block this [`AllocEntry`] refers to
    index: Le<u64>,

    /// The number of blocks after (and including) `index` that are are free or used.
    /// If negative, they are used; if positive, they are free.
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

/// A node in the allocation chain.
///
/// This struct represents a block containing a list of allocation entries.
/// These blocks are chained together to form a log of allocation operations.
#[repr(C, packed)]
pub struct AllocList {
    /// A pointer to the previous AllocList.
    /// If this is the null pointer, this is the first element of the chain.
    pub prev: BlockPtr<AllocList>,

    /// Allocation entries.
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

#[test]
fn allocator_test() {
    let mut alloc = Allocator::default();

    assert_eq!(alloc.allocate(BlockMeta::default()), None);

    alloc.deallocate(unsafe { BlockAddr::new(1, BlockMeta::default()) });
    assert_eq!(
        alloc.allocate(BlockMeta::default()),
        Some(unsafe { BlockAddr::new(1, BlockMeta::default()) })
    );
    assert_eq!(alloc.allocate(BlockMeta::default()), None);

    for addr in 1023..2048 {
        alloc.deallocate(unsafe { BlockAddr::new(addr, BlockMeta::default()) });
    }

    // Lazy coalescing means blocks stay in level 0
    assert!(alloc.levels.len() >= 1);
    let expected: BTreeSet<u64> = (1023..2048).collect();
    assert_eq!(alloc.levels[0], expected);
    
    // Higher levels should be empty
    for level in 1..alloc.levels.len() {
        assert_eq!(alloc.levels[level], BTreeSet::new());
    }

    for addr in 1023..2048 {
        assert_eq!(
            alloc.allocate(BlockMeta::default()),
            Some(unsafe { BlockAddr::new(addr, BlockMeta::default()) })
        );
    }
    assert_eq!(alloc.allocate(BlockMeta::default()), None);

    for level in 0..alloc.levels.len() {
        assert_eq!(alloc.levels[level], BTreeSet::new());
    }
}

#[test]
fn coalescing_test() {
    let mut alloc = Allocator::default();

    // Deallocate two adjacent L0 blocks. 
    // Due to lazy coalescing, they stay in L0.
    alloc.deallocate(unsafe { BlockAddr::new(0, BlockMeta::new(BlockLevel(0))) });
    alloc.deallocate(unsafe { BlockAddr::new(1, BlockMeta::new(BlockLevel(0))) });

    assert!(alloc.levels.len() >= 1);
    assert_eq!(alloc.levels[0].len(), 2);

    // Allocate L1 block (requires 2 L0 blocks).
    // This should trigger coalescing.
    let addr = alloc.allocate(BlockMeta::new(BlockLevel(1)));
    
    assert_eq!(addr, Some(unsafe { BlockAddr::new(0, BlockMeta::new(BlockLevel(1))) }));
    
    // Verify levels are empty (consumed)
    for level in 0..alloc.levels.len() {
        assert!(alloc.levels[level].is_empty());
    }
}

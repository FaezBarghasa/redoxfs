//! Metadata sharding for multi-disk arrays.
//!
//! When RedoxFS spans multiple disks, directory metadata can be sharded across
//! disks to distribute I/O and reduce contention. This module provides the
//! shard selection logic and a sharded allocator wrapper.

use crate::Allocator;
use crate::{BlockAddr, BlockMeta};

/// Compute the shard index for a given inode ID across `num_disks` disks.
///
/// Uses SeaHash of the inode ID modulo the number of disks to produce a
/// deterministic, uniform distribution of inodes across shards.
pub fn shard_for_inode(inode_id: u64, num_disks: usize) -> usize {
    if num_disks <= 1 {
        return 0;
    }
    (seahash::hash(&inode_id.to_le_bytes()) as usize) % num_disks
}

/// A mapping from inode ranges to disk indices for metadata sharding.
///
/// In a multi-disk array, the `ShardMap` determines which disk should store
/// the metadata for a given inode. This enables parallel metadata operations
/// across disks, reducing contention on any single allocator.
pub struct ShardMap {
    num_disks: usize,
}

impl ShardMap {
    /// Create a new `ShardMap` for the given number of disks.
    pub fn new(num_disks: usize) -> Self {
        assert!(num_disks > 0, "num_disks must be at least 1");
        Self { num_disks }
    }

    /// Get the number of disks.
    pub fn num_disks(&self) -> usize {
        self.num_disks
    }

    /// Determine which disk shard an inode belongs to.
    pub fn shard(&self, inode_id: u64) -> usize {
        shard_for_inode(inode_id, self.num_disks)
    }

    /// Returns true if sharding is active (more than one disk).
    pub fn is_sharded(&self) -> bool {
        self.num_disks > 1
    }
}

/// A sharded allocator wrapping multiple per-disk `Allocator` instances.
///
/// When `num_disks == 1`, this simply delegates to the single allocator.
/// When `num_disks > 1`, allocation requests are routed to the appropriate
/// shard based on the inode ID.
pub struct ShardedAllocator {
    allocators: alloc::vec::Vec<Allocator>,
    shard_map: ShardMap,
}

impl ShardedAllocator {
    /// Create a new sharded allocator with the specified number of disk shards.
    pub fn new(num_disks: usize) -> Self {
        let mut allocators = alloc::vec::Vec::with_capacity(num_disks);
        for _ in 0..num_disks {
            allocators.push(Allocator::default());
        }
        Self {
            allocators,
            shard_map: ShardMap::new(num_disks),
        }
    }

    /// Get the shard map.
    pub fn shard_map(&self) -> &ShardMap {
        &self.shard_map
    }

    /// Get a mutable reference to the allocator for the given shard.
    pub fn allocator_mut(&mut self, shard_idx: usize) -> &mut Allocator {
        &mut self.allocators[shard_idx]
    }

    /// Get an immutable reference to the allocator for the given shard.
    pub fn allocator(&self, shard_idx: usize) -> &Allocator {
        &self.allocators[shard_idx]
    }

    /// Allocate a block from the shard corresponding to the given inode ID.
    pub fn allocate_for_inode(&mut self, inode_id: u64, meta: BlockMeta) -> Option<BlockAddr> {
        let shard = self.shard_map.shard(inode_id);
        self.allocators[shard].allocate(meta)
    }

    /// Deallocate a block from the shard corresponding to the given inode ID.
    pub fn deallocate_for_inode(&mut self, inode_id: u64, addr: BlockAddr) {
        let shard = self.shard_map.shard(inode_id);
        self.allocators[shard].deallocate(addr);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_disk_shard_always_zero() {
        for inode_id in 0..1000 {
            assert_eq!(shard_for_inode(inode_id, 1), 0);
        }
    }

    #[test]
    fn multi_disk_shard_distributes() {
        let num_disks = 4;
        let mut counts = [0usize; 4];
        for inode_id in 0..10000 {
            let shard = shard_for_inode(inode_id, num_disks);
            assert!(shard < num_disks);
            counts[shard] += 1;
        }

        // Each shard should get a reasonable share (at least 10% given uniform hash)
        for count in &counts {
            assert!(
                *count > 1000,
                "Shard distribution is too uneven: {:?}",
                counts
            );
        }
    }

    #[test]
    fn shard_deterministic() {
        // Same inode_id should always land on the same shard
        for inode_id in 0..100 {
            let s1 = shard_for_inode(inode_id, 8);
            let s2 = shard_for_inode(inode_id, 8);
            assert_eq!(s1, s2, "Shard should be deterministic for inode {inode_id}");
        }
    }

    #[test]
    fn shard_map_basics() {
        let map = ShardMap::new(4);
        assert_eq!(map.num_disks(), 4);
        assert!(map.is_sharded());

        let map1 = ShardMap::new(1);
        assert!(!map1.is_sharded());
    }

    #[test]
    fn sharded_allocator_creation() {
        let sa = ShardedAllocator::new(4);
        assert_eq!(sa.shard_map().num_disks(), 4);
    }
}

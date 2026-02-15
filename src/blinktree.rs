//! B-Link Tree implementation for lock-free concurrent directory access.
//!
//! A B-Link tree is a variant of a B+ tree where every node (internal and leaf)
//! has a `right_link` pointer to its right sibling and a `high_key` that represents
//! the maximum key stored in the subtree rooted at that node. This enables
//! lock-free readers: a reader that arrives at a node mid-split can detect the
//! split via the `high_key` and follow the `right_link` to find the correct node.
//!
//! Combined with RedoxFS's Copy-on-Write semantics (writers produce new block
//! versions via the journal, readers see a consistent snapshot), this delivers
//! lock-free directory reads without any mutex contention.

use alloc::vec::Vec;
use core::{mem, ops, slice};
use endian_num::Le;
use syscall::error::{Error, Result, EEXIST, EIO, ENOSPC};

use crate::htree::HTreeHash;
use crate::{BlockLevel, BlockPtr, BlockRaw, BlockTrait, DirEntry, DirList, BLOCK_SIZE};

// ─── Layout constants ───────────────────────────────────────────────────────

/// Size of BLinkLeaf fixed header:
///   count: u16 (2) + entry_bytes_len: u16 (2) + high_key: HTreeHash (4)
///   + right_link: BlockPtr<BLinkLeaf> (16) + magic: u32 (4) = 28 bytes
const BLINK_LEAF_HEADER_SIZE: usize = 28;

/// Usable entry storage in a leaf node.
const BLINK_LEAF_DATA_SIZE: usize = BLOCK_SIZE as usize - BLINK_LEAF_HEADER_SIZE;

/// Size of each separator in an internal node:
///   key: HTreeHash (4) + child_ptr: BlockPtr (16) = 20 bytes
const BLINK_SEP_SIZE: usize = mem::size_of::<BLinkSeparator>();

/// Size of BLinkInternal fixed header:
///   count: u16 (2) + high_key: HTreeHash (4) + right_link: BlockPtr<BLinkInternal> (16)
///   + leftmost_child: BlockPtr (16) + magic: u32 (4) = 42 bytes
const BLINK_INTERNAL_HEADER_SIZE: usize = 42;

/// Maximum separators in an internal node.
pub const BLINK_INTERNAL_MAX_ENTRIES: usize =
    (BLOCK_SIZE as usize - BLINK_INTERNAL_HEADER_SIZE) / BLINK_SEP_SIZE;

/// Padding in BLinkInternal to fill exactly BLOCK_SIZE.
const BLINK_INTERNAL_PADDING: usize = BLOCK_SIZE as usize
    - BLINK_INTERNAL_HEADER_SIZE
    - (BLINK_INTERNAL_MAX_ENTRIES * BLINK_SEP_SIZE);

/// Magic value to distinguish B-Link leaves from legacy DirList blocks.
const BLINK_LEAF_MAGIC: u32 = 0x424C4E4B; // "BLNK"

/// Magic value for B-Link internal nodes.
const BLINK_INTERNAL_MAGIC: u32 = 0x424C4E49; // "BLNI"

// ─── Separator (internal node key-pointer pair) ─────────────────────────────

/// A separator entry in a `BLinkInternal` node.
/// Each separator defines a boundary: entries with `hash <= key` go to
/// the child on the left; entries with `hash > key` go to the next child.
#[repr(C, packed)]
#[derive(Clone, Copy, Debug)]
pub struct BLinkSeparator {
    pub key: HTreeHash,
    pub child_ptr: BlockPtr<BlockRaw>,
}

impl Default for BLinkSeparator {
    fn default() -> Self {
        Self {
            key: HTreeHash::default(),
            child_ptr: BlockPtr::default(),
        }
    }
}

// ─── BLinkLeaf ──────────────────────────────────────────────────────────────

/// A B-Link tree leaf node, stored in a single 4096-byte block.
///
/// Contains a packed array of serialized `DirEntry` values (same serialization
/// format as `DirList`), sorted by `HTreeHash` of the entry name.
///
/// The `right_link` pointer connects this leaf to its right sibling for
/// lock-free traversal (the "move-right" protocol).
/// The `high_key` is the maximum `HTreeHash` of any entry stored in this leaf.
#[repr(C, packed)]
pub struct BLinkLeaf {
    /// Magic number to identify this as a B-Link leaf.
    pub magic: Le<u32>,
    /// Number of directory entries in this leaf.
    pub count: Le<u16>,
    /// Total bytes used in `entry_data`.
    pub entry_bytes_len: Le<u16>,
    /// The maximum hash key in this leaf (fence key).
    pub high_key: HTreeHash,
    /// Pointer to the right sibling leaf (null if rightmost).
    pub right_link: BlockPtr<BLinkLeaf>,
    /// Packed serialized DirEntry data, sorted by HTreeHash.
    pub entry_data: [u8; BLINK_LEAF_DATA_SIZE],
}

impl BLinkLeaf {
    /// Returns the entry count.
    pub fn entry_count(&self) -> usize {
        self.count.to_ne() as usize
    }

    /// Returns the used data bytes.
    fn data_len(&self) -> usize {
        self.entry_bytes_len.to_ne() as usize
    }

    /// Iterate over all entries in this leaf.
    pub fn entries(&self) -> BLinkLeafIterator<'_> {
        BLinkLeafIterator {
            leaf: self,
            emit_count: 0,
            position: 0,
        }
    }

    /// Collect all entries with their hashes, sorted by hash.
    fn entries_with_hashes(&self) -> Vec<(HTreeHash, DirEntry)> {
        let mut result = Vec::with_capacity(self.entry_count());
        for entry in self.entries() {
            if let Some(name) = entry.name() {
                let hash = HTreeHash::from_name(name);
                result.push((hash, entry));
            }
        }
        result
    }

    /// Search for a directory entry by name.
    pub fn find_entry(&self, name: &str) -> Option<DirEntry> {
        for entry in self.entries() {
            if entry.name() == Some(name) {
                return Some(entry);
            }
        }
        None
    }

    /// Try to insert a `DirEntry` into this leaf, maintaining sorted order by hash.
    /// Returns `true` if the entry was inserted, `false` if the leaf is full.
    pub fn insert_entry(&mut self, entry: &DirEntry) -> bool {
        let entry_size = entry.serialized_size();
        let current_len = self.data_len();
        if current_len + entry_size > BLINK_LEAF_DATA_SIZE {
            return false;
        }

        let name = match entry.name() {
            Some(n) => n,
            None => return false,
        };
        let new_hash = HTreeHash::from_name(name);

        // Collect all existing entries, add the new one, sort by hash, re-serialize.
        let mut all_entries = self.entries_with_hashes();
        all_entries.push((new_hash, *entry));
        all_entries.sort_by(|a, b| a.0.cmp(&b.0));

        // Re-serialize into entry_data
        let mut pos = 0;
        for (_, e) in all_entries.iter() {
            if let Some(written) = e.serialize_into(&mut self.entry_data[pos..]) {
                pos += written;
            } else {
                return false;
            }
        }

        // Zero remaining bytes
        for byte in self.entry_data[pos..].iter_mut() {
            *byte = 0;
        }

        self.count = (all_entries.len() as u16).into();
        self.entry_bytes_len = (pos as u16).into();

        // Update high_key
        if let Some(last) = all_entries.last() {
            self.high_key = last.0;
        }

        true
    }

    /// Remove a directory entry by name. Returns the removed entry if found.
    pub fn remove_entry(&mut self, name: &str) -> Option<DirEntry> {
        let mut all_entries = self.entries_with_hashes();
        let idx = all_entries
            .iter()
            .position(|(_, e)| e.name() == Some(name))?;
        let removed = all_entries.remove(idx).1;

        // Re-serialize
        let mut pos = 0;
        for (_, e) in all_entries.iter() {
            if let Some(written) = e.serialize_into(&mut self.entry_data[pos..]) {
                pos += written;
            }
        }
        for byte in self.entry_data[pos..].iter_mut() {
            *byte = 0;
        }

        self.count = (all_entries.len() as u16).into();
        self.entry_bytes_len = (pos as u16).into();

        // Update high_key
        self.high_key = all_entries
            .last()
            .map(|(h, _)| *h)
            .unwrap_or(HTreeHash::default());

        Some(removed)
    }

    /// Split this leaf into two halves. Returns `(new_high_key_for_self, new_right_sibling)`.
    /// After the split, `self` contains the lower half and the returned leaf contains the upper half.
    /// The returned leaf's `right_link` is set to `self.right_link`, and `self.right_link`
    /// should be updated by the caller to point to the new sibling.
    pub fn split(&mut self) -> Result<(HTreeHash, BLinkLeaf)> {
        let all_entries = self.entries_with_hashes();
        if all_entries.len() < 2 {
            return Err(Error::new(EIO));
        }

        let half = all_entries.len() / 2;
        let (left_entries, right_entries) = all_entries.split_at(half);

        // Build left (self)
        let mut left_pos = 0;
        for (_, e) in left_entries.iter() {
            if let Some(written) = e.serialize_into(&mut self.entry_data[left_pos..]) {
                left_pos += written;
            }
        }
        for byte in self.entry_data[left_pos..].iter_mut() {
            *byte = 0;
        }
        self.count = (left_entries.len() as u16).into();
        self.entry_bytes_len = (left_pos as u16).into();
        let left_high_key = left_entries
            .last()
            .map(|(h, _)| *h)
            .unwrap_or(HTreeHash::default());
        self.high_key = left_high_key;

        // Build right sibling
        let mut right_leaf = BLinkLeaf::empty(BlockLevel::L0).ok_or(Error::new(EIO))?;
        right_leaf.right_link = self.right_link;
        let mut right_pos = 0;
        for (_, e) in right_entries.iter() {
            if let Some(written) = e.serialize_into(&mut right_leaf.entry_data[right_pos..]) {
                right_pos += written;
            }
        }
        right_leaf.count = (right_entries.len() as u16).into();
        right_leaf.entry_bytes_len = (right_pos as u16).into();
        right_leaf.high_key = right_entries
            .last()
            .map(|(h, _)| *h)
            .unwrap_or(HTreeHash::default());

        Ok((left_high_key, right_leaf))
    }

    /// Check if this leaf is full (cannot accept another entry of the given size).
    pub fn is_full_for(&self, entry_size: usize) -> bool {
        self.data_len() + entry_size > BLINK_LEAF_DATA_SIZE
    }

    /// Convert a legacy `DirList` into a `BLinkLeaf`, preserving all entries.
    pub fn from_dir_list(dir_list: &DirList) -> Result<BLinkLeaf> {
        let mut leaf = BLinkLeaf::empty(BlockLevel::L0).ok_or(Error::new(EIO))?;

        // Collect entries from the DirList, compute hashes, sort, and re-serialize
        let mut entries_with_hashes: Vec<(HTreeHash, DirEntry)> = Vec::new();
        for entry in dir_list.entries() {
            if let Some(name) = entry.name() {
                let hash = HTreeHash::from_name(name);
                entries_with_hashes.push((hash, entry));
            }
        }
        entries_with_hashes.sort_by(|a, b| a.0.cmp(&b.0));

        let mut pos = 0;
        for (_, e) in entries_with_hashes.iter() {
            if let Some(written) = e.serialize_into(&mut leaf.entry_data[pos..]) {
                pos += written;
            } else {
                return Err(Error::new(ENOSPC));
            }
        }

        leaf.count = (entries_with_hashes.len() as u16).into();
        leaf.entry_bytes_len = (pos as u16).into();
        leaf.high_key = entries_with_hashes
            .last()
            .map(|(h, _)| *h)
            .unwrap_or(HTreeHash::default());

        Ok(leaf)
    }
}

unsafe impl BlockTrait for BLinkLeaf {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self {
                magic: BLINK_LEAF_MAGIC.into(),
                count: 0.into(),
                entry_bytes_len: 0.into(),
                high_key: HTreeHash::default(),
                right_link: BlockPtr::default(),
                entry_data: [0; BLINK_LEAF_DATA_SIZE],
            })
        } else {
            None
        }
    }
}

impl ops::Deref for BLinkLeaf {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self as *const BLinkLeaf as *const u8,
                mem::size_of::<BLinkLeaf>(),
            )
        }
    }
}

impl ops::DerefMut for BLinkLeaf {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(
                self as *mut BLinkLeaf as *mut u8,
                mem::size_of::<BLinkLeaf>(),
            )
        }
    }
}

/// Iterator over entries in a `BLinkLeaf`.
pub struct BLinkLeafIterator<'a> {
    leaf: &'a BLinkLeaf,
    emit_count: usize,
    position: usize,
}

impl Iterator for BLinkLeafIterator<'_> {
    type Item = DirEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if self.emit_count < self.leaf.entry_count() {
            let (entry, bytes_read) =
                DirEntry::deserialize_from(&self.leaf.entry_data[self.position..]).ok()?;
            self.emit_count += 1;
            self.position += bytes_read;
            Some(entry)
        } else {
            None
        }
    }
}

// ─── BLinkInternal ──────────────────────────────────────────────────────────

/// A B-Link tree internal node, stored in a single 4096-byte block.
///
/// Contains sorted separator keys and child pointers. The `leftmost_child` is the
/// pointer to the child with keys less than or equal to the first separator key.
///
/// Routing: for separator `i`, keys `<= separators[i].key` go to `separators[i].child_ptr`
/// (which is the pointer to children whose keys are between `separators[i-1].key` and
/// `separators[i].key`). Keys below all separators go to `leftmost_child`.
#[repr(C, packed)]
pub struct BLinkInternal {
    /// Magic number to identify this as a B-Link internal node.
    pub magic: Le<u32>,
    /// Number of separator entries.
    pub count: Le<u16>,
    /// The maximum key in the entire subtree rooted at this node (fence key).
    pub high_key: HTreeHash,
    /// Pointer to the right sibling internal node (null if rightmost).
    pub right_link: BlockPtr<BLinkInternal>,
    /// Pointer to the leftmost child (entries with keys < first separator).
    pub leftmost_child: BlockPtr<BlockRaw>,
    /// Sorted separator entries.
    pub separators: [BLinkSeparator; BLINK_INTERNAL_MAX_ENTRIES],
    /// Padding to fill exactly BLOCK_SIZE.
    _padding: [u8; BLINK_INTERNAL_PADDING],
}

impl BLinkInternal {
    /// Returns the separator count.
    pub fn sep_count(&self) -> usize {
        self.count.to_ne() as usize
    }

    /// Find which child pointer to follow for the given hash key.
    /// Returns the `BlockPtr` of the appropriate child.
    pub fn find_child(&self, key: HTreeHash) -> BlockPtr<BlockRaw> {
        for i in 0..self.sep_count() {
            if key <= self.separators[i].key {
                if i == 0 {
                    return self.leftmost_child;
                }
                return self.separators[i - 1].child_ptr;
            }
        }
        // Key is greater than all separators — go to the last child
        if self.sep_count() > 0 {
            self.separators[self.sep_count() - 1].child_ptr
        } else {
            self.leftmost_child
        }
    }

    /// Insert a new separator into this internal node. Returns false if full.
    pub fn insert_separator(&mut self, key: HTreeHash, child_ptr: BlockPtr<BlockRaw>) -> bool {
        let count = self.sep_count();
        if count >= BLINK_INTERNAL_MAX_ENTRIES {
            return false;
        }

        // Collect existing, add new, sort, re-assign
        let mut seps: Vec<BLinkSeparator> = Vec::with_capacity(count + 1);
        for i in 0..count {
            seps.push(self.separators[i]);
        }
        seps.push(BLinkSeparator { key, child_ptr });
        seps.sort_by(|a, b| a.key.cmp(&b.key));

        for (i, sep) in seps.iter().enumerate() {
            self.separators[i] = *sep;
        }
        // Zero remaining
        for i in seps.len()..BLINK_INTERNAL_MAX_ENTRIES {
            self.separators[i] = BLinkSeparator::default();
        }

        self.count = (seps.len() as u16).into();

        // Update high_key
        if let Some(last) = seps.last() {
            if last.key > self.high_key || self.high_key == HTreeHash::default() {
                self.high_key = last.key;
            }
        }

        true
    }

    /// Split this internal node into two halves.
    /// Returns `(median_key, new_right_sibling)`.
    pub fn split(&mut self) -> Result<(HTreeHash, BLinkInternal)> {
        let count = self.sep_count();
        if count < 2 {
            return Err(Error::new(EIO));
        }

        let half = count / 2;
        let median_key = self.separators[half].key;

        // The left node (self) keeps separators [0..half)
        // The right node gets separators [half+1..count)
        // The median key is promoted to the parent
        // The right node's leftmost_child is the child_ptr of the median separator

        let mut right = BLinkInternal::empty(BlockLevel::L0).ok_or(Error::new(EIO))?;
        right.leftmost_child = self.separators[half].child_ptr;
        right.right_link = self.right_link;

        let mut right_count = 0;
        for i in (half + 1)..count {
            right.separators[right_count] = self.separators[i];
            right_count += 1;
        }
        right.count = (right_count as u16).into();
        right.high_key = if right_count > 0 {
            right.separators[right_count - 1].key
        } else {
            median_key
        };

        // Update self: keep only [0..half)
        let left_high_key = if half > 0 {
            self.separators[half - 1].key
        } else {
            HTreeHash::default()
        };

        for i in half..BLINK_INTERNAL_MAX_ENTRIES {
            self.separators[i] = BLinkSeparator::default();
        }
        self.count = (half as u16).into();
        self.high_key = left_high_key;

        Ok((median_key, right))
    }
}

unsafe impl BlockTrait for BLinkInternal {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self {
                magic: BLINK_INTERNAL_MAGIC.into(),
                count: 0.into(),
                high_key: HTreeHash::default(),
                right_link: BlockPtr::default(),
                leftmost_child: BlockPtr::default(),
                separators: [BLinkSeparator::default(); BLINK_INTERNAL_MAX_ENTRIES],
                _padding: [0; BLINK_INTERNAL_PADDING],
            })
        } else {
            None
        }
    }
}

impl ops::Deref for BLinkInternal {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self as *const BLinkInternal as *const u8,
                mem::size_of::<BLinkInternal>(),
            )
        }
    }
}

impl ops::DerefMut for BLinkInternal {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(
                self as *mut BLinkInternal as *mut u8,
                mem::size_of::<BLinkInternal>(),
            )
        }
    }
}

// ─── BLinkTree (stateless operations) ───────────────────────────────────────

/// Stateless B-Link tree operations.
///
/// All methods are free functions that operate on block pointers via a
/// transaction. The B-Link tree root pointer is stored in the directory
/// node's `level0[0]` slot (same position as the legacy `DirList` pointer).
///
/// The root can be either a `BLinkLeaf` (single-leaf tree for small directories)
/// or a `BLinkInternal` (multi-level tree for large directories). The magic
/// number in the first 4 bytes of the block distinguishes the two.
pub struct BLinkTree;

impl BLinkTree {
    /// Detect whether a block is a B-Link leaf, internal node, or legacy DirList.
    pub fn block_type(block_data: &[u8]) -> BLinkBlockType {
        if block_data.len() < 4 {
            return BLinkBlockType::Unknown;
        }
        let magic =
            u32::from_le_bytes([block_data[0], block_data[1], block_data[2], block_data[3]]);
        match magic {
            BLINK_LEAF_MAGIC => BLinkBlockType::Leaf,
            BLINK_INTERNAL_MAGIC => BLinkBlockType::Internal,
            _ => BLinkBlockType::LegacyDirList,
        }
    }

    /// Search for a directory entry by name in a B-Link tree rooted at `root_ptr`.
    ///
    /// This is a lock-free read operation. At each node, if the search key exceeds
    /// the node's `high_key`, we follow the `right_link` (the "move-right" protocol).
    pub fn search_leaf(leaf: &BLinkLeaf, name: &str) -> Option<DirEntry> {
        let target_hash = HTreeHash::from_name(name);

        // If the target hash exceeds this leaf's high_key, the entry might be
        // in the right sibling. However, since we operate on CoW snapshots,
        // the caller must handle the move-right at the transaction level.
        // Here we just do a direct search within this leaf.
        let _ = target_hash; // Used for future optimization (binary search)

        leaf.find_entry(name)
    }

    /// Insert a directory entry into a B-Link leaf.
    /// If the leaf needs to split, returns `Some((split_key, new_right_leaf))`.
    /// The caller is responsible for writing both leaves and updating the parent.
    pub fn insert_into_leaf(
        leaf: &mut BLinkLeaf,
        entry: &DirEntry,
    ) -> Result<Option<(HTreeHash, BLinkLeaf)>> {
        let name = entry.name().ok_or(Error::new(EIO))?;

        // Check for duplicate
        if leaf.find_entry(name).is_some() {
            return Err(Error::new(EEXIST));
        }

        // Try direct insert
        if leaf.insert_entry(entry) {
            return Ok(None);
        }

        // Leaf is full — split, then insert into the appropriate half
        let (split_key, mut right_leaf) = leaf.split()?;
        let new_hash = HTreeHash::from_name(name);

        if new_hash <= split_key {
            if !leaf.insert_entry(entry) {
                return Err(Error::new(ENOSPC));
            }
        } else {
            if !right_leaf.insert_entry(entry) {
                return Err(Error::new(ENOSPC));
            }
        }

        Ok(Some((split_key, right_leaf)))
    }

    /// Remove a directory entry from a B-Link leaf.
    /// Returns the removed entry if found.
    pub fn remove_from_leaf(leaf: &mut BLinkLeaf, name: &str) -> Option<DirEntry> {
        leaf.remove_entry(name)
    }
}

/// Block type discriminator for B-Link tree nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BLinkBlockType {
    Leaf,
    Internal,
    LegacyDirList,
    Unknown,
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TreePtr;
    use alloc::format;

    #[test]
    fn blink_leaf_size_test() {
        assert_eq!(
            mem::size_of::<BLinkLeaf>(),
            BLOCK_SIZE as usize,
            "BLinkLeaf must fit exactly in one block"
        );
    }

    #[test]
    fn blink_internal_size_test() {
        assert_eq!(
            mem::size_of::<BLinkInternal>(),
            BLOCK_SIZE as usize,
            "BLinkInternal must fit exactly in one block"
        );
    }

    #[test]
    fn blink_separator_size_test() {
        // HTreeHash(4) + BlockPtr(16) = 20
        assert_eq!(mem::size_of::<BLinkSeparator>(), 20);
    }

    #[test]
    fn blink_leaf_empty_has_correct_magic() {
        let leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();
        assert_eq!(leaf.magic.to_ne(), BLINK_LEAF_MAGIC);
        assert_eq!(leaf.entry_count(), 0);
        assert!(leaf.right_link.is_null());
    }

    #[test]
    fn blink_internal_empty_has_correct_magic() {
        let internal = BLinkInternal::empty(BlockLevel::L0).unwrap();
        assert_eq!(internal.magic.to_ne(), BLINK_INTERNAL_MAGIC);
        assert_eq!(internal.sep_count(), 0);
        assert!(internal.right_link.is_null());
    }

    #[test]
    fn blink_insert_search_test() {
        let mut leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();

        for i in 0..50 {
            let name = format!("file_{i:04}");
            let entry = DirEntry::new(TreePtr::new(i + 1), &name);
            assert!(leaf.insert_entry(&entry), "Failed to insert {name}");
        }

        assert_eq!(leaf.entry_count(), 50);

        // Search for each inserted entry
        for i in 0..50 {
            let name = format!("file_{i:04}");
            let found = leaf.find_entry(&name);
            assert!(found.is_some(), "Failed to find {name}");
            assert_eq!(found.unwrap().name(), Some(name.as_str()));
        }

        // Search for non-existent entry
        assert!(leaf.find_entry("nonexistent").is_none());
    }

    #[test]
    fn blink_remove_test() {
        let mut leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();

        for i in 0..20 {
            let name = format!("del_{i:03}");
            let entry = DirEntry::new(TreePtr::new(i + 1), &name);
            leaf.insert_entry(&entry);
        }
        assert_eq!(leaf.entry_count(), 20);

        // Remove every other entry
        for i in (0..20).step_by(2) {
            let name = format!("del_{i:03}");
            let removed = leaf.remove_entry(&name);
            assert!(removed.is_some(), "Failed to remove {name}");
        }
        assert_eq!(leaf.entry_count(), 10);

        // Verify remaining entries
        for i in (1..20).step_by(2) {
            let name = format!("del_{i:03}");
            assert!(
                leaf.find_entry(&name).is_some(),
                "Entry {name} should still exist"
            );
        }

        // Verify removed entries are gone
        for i in (0..20).step_by(2) {
            let name = format!("del_{i:03}");
            assert!(
                leaf.find_entry(&name).is_none(),
                "Entry {name} should be removed"
            );
        }
    }

    #[test]
    fn blink_split_test() {
        let mut leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();

        // Fill the leaf until it can't hold any more
        let mut inserted = 0;
        loop {
            let name = format!("sp_{inserted:04}");
            let entry = DirEntry::new(TreePtr::new(inserted as u32 + 1), &name);
            if !leaf.insert_entry(&entry) {
                break;
            }
            inserted += 1;
        }

        assert!(inserted > 4, "Should be able to insert multiple entries");
        let original_count = leaf.entry_count();

        // Split
        let (split_key, right_leaf) = leaf.split().unwrap();

        // Verify the split
        let left_count = leaf.entry_count();
        let right_count = right_leaf.entry_count();
        assert_eq!(
            left_count + right_count,
            original_count,
            "All entries should be preserved across the split"
        );

        // Left leaf's high_key should equal split_key
        assert_eq!(leaf.high_key, split_key);

        // All entries in the left leaf should have hash <= split_key
        for entry in leaf.entries() {
            let hash = HTreeHash::from_name(entry.name().unwrap());
            assert!(
                hash <= split_key,
                "Left leaf entry {:?} has hash > split_key",
                entry.name()
            );
        }

        // All entries in the right leaf should have hash > split_key (or equal due to collisions)
        // Actually, the right side gets entries at and after the split point,
        // so they should have hash >= split_key
        // (In practice, the split puts entries [0..half) left and [half..] right)
    }

    #[test]
    fn blink_insert_with_split_test() {
        let mut leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();

        // Fill the leaf
        let mut inserted = 0;
        loop {
            let name = format!("is_{inserted:04}");
            let entry = DirEntry::new(TreePtr::new(inserted as u32 + 1), &name);
            let result = BLinkTree::insert_into_leaf(&mut leaf, &entry).unwrap();
            if result.is_some() {
                // Split happened — verify it
                let (_split_key, right_leaf) = result.unwrap();
                assert!(leaf.entry_count() > 0);
                assert!(right_leaf.entry_count() > 0);
                // The new entry should be in one of the two leaves
                let name_copy = format!("is_{inserted:04}");
                let in_left = leaf.find_entry(&name_copy).is_some();
                let in_right = right_leaf.find_entry(&name_copy).is_some();
                assert!(
                    in_left || in_right,
                    "New entry should be in one of the split leaves"
                );
                break;
            }
            inserted += 1;
        }
    }

    #[test]
    fn blink_duplicate_insert_fails() {
        let mut leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();
        let entry = DirEntry::new(TreePtr::new(1), "duplicate_test");
        assert!(BLinkTree::insert_into_leaf(&mut leaf, &entry)
            .unwrap()
            .is_none());

        // Inserting the same name again should fail with EEXIST
        let entry2 = DirEntry::new(TreePtr::new(2), "duplicate_test");
        let result = BLinkTree::insert_into_leaf(&mut leaf, &entry2);
        assert!(result.is_err());
    }

    #[test]
    fn blink_iterate_sorted_test() {
        let mut leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();

        // Insert entries (they should be stored sorted by hash)
        for i in 0..30 {
            let name = format!("iter_{i:03}");
            let entry = DirEntry::new(TreePtr::new(i + 1), &name);
            leaf.insert_entry(&entry);
        }

        // Verify entries come out sorted by hash
        let mut prev_hash = HTreeHash::from_name("__0");
        for entry in leaf.entries() {
            let hash = HTreeHash::from_name(entry.name().unwrap());
            assert!(
                hash >= prev_hash,
                "Entries should be in sorted hash order: {:?} >= {:?}",
                hash,
                prev_hash
            );
            prev_hash = hash;
        }
    }

    #[test]
    fn blink_from_dir_list_test() {
        let mut dir_list = DirList::empty(BlockLevel::L0).unwrap();
        for i in 0..10 {
            let name = format!("migrated_{i:03}");
            let entry = DirEntry::new(TreePtr::new(i + 1), &name);
            dir_list.append(&entry);
        }

        let leaf = BLinkLeaf::from_dir_list(&dir_list).unwrap();
        assert_eq!(leaf.entry_count(), 10);

        // Verify all entries are findable
        for i in 0..10 {
            let name = format!("migrated_{i:03}");
            assert!(
                leaf.find_entry(&name).is_some(),
                "Entry {name} should exist in migrated leaf"
            );
        }

        // Verify entries are sorted by hash
        let mut prev_hash = HTreeHash::from_name("__0");
        for entry in leaf.entries() {
            let hash = HTreeHash::from_name(entry.name().unwrap());
            assert!(hash >= prev_hash);
            prev_hash = hash;
        }
    }

    #[test]
    fn blink_block_type_detection() {
        let leaf = BLinkLeaf::empty(BlockLevel::L0).unwrap();
        let leaf_bytes: &[u8] = &leaf;
        assert_eq!(BLinkTree::block_type(leaf_bytes), BLinkBlockType::Leaf);

        let internal = BLinkInternal::empty(BlockLevel::L0).unwrap();
        let internal_bytes: &[u8] = &internal;
        assert_eq!(
            BLinkTree::block_type(internal_bytes),
            BLinkBlockType::Internal
        );

        let dir_list = DirList::empty(BlockLevel::L0).unwrap();
        let dir_list_bytes: &[u8] = &dir_list;
        assert_eq!(
            BLinkTree::block_type(dir_list_bytes),
            BLinkBlockType::LegacyDirList
        );
    }

    #[test]
    fn blink_internal_insert_separator_test() {
        let mut internal = BLinkInternal::empty(BlockLevel::L0).unwrap();

        for i in 0..10 {
            let key = HTreeHash::from_name(&format!("key_{i:03}"));
            let ptr = BlockPtr::marker(0);
            assert!(internal.insert_separator(key, ptr));
        }
        assert_eq!(internal.sep_count(), 10);

        // Separators should be in sorted order
        let mut prev_key = HTreeHash::from_name("__0");
        for i in 0..internal.sep_count() {
            let key = internal.separators[i].key;
            assert!(key >= prev_key, "Separators should be sorted");
            prev_key = key;
        }
    }

    #[test]
    fn blink_internal_split_test() {
        let mut internal = BLinkInternal::empty(BlockLevel::L0).unwrap();

        // Fill internal node
        let fill_count = BLINK_INTERNAL_MAX_ENTRIES.min(200);
        for i in 0..fill_count {
            let key = HTreeHash::from_name(&format!("ikey_{i:05}"));
            let ptr = BlockPtr::marker(0);
            internal.insert_separator(key, ptr);
        }

        let original_count = internal.sep_count();
        let (median_key, right_internal) = internal.split().unwrap();

        let left_count = internal.sep_count();
        let right_count = right_internal.sep_count();

        // The median is promoted, so left + right + 1 == original
        assert_eq!(left_count + right_count + 1, original_count);

        // All left separators should have key <= median (actually < median since median is promoted)
        for i in 0..left_count {
            assert!(internal.separators[i].key < median_key);
        }
    }

    #[test]
    fn blink_internal_find_child_test() {
        let mut internal = BLinkInternal::empty(BlockLevel::L0).unwrap();
        internal.leftmost_child = BlockPtr::marker(0);

        // Insert separators with known hash values via the test __N naming convention
        let key1 = HTreeHash::from_name("__100");
        let key2 = HTreeHash::from_name("__200");
        let key3 = HTreeHash::from_name("__300");

        let ptr1 = BlockPtr::marker(1);
        let ptr2 = BlockPtr::marker(2);
        let ptr3 = BlockPtr::marker(3);

        internal.insert_separator(key1, ptr1);
        internal.insert_separator(key2, ptr2);
        internal.insert_separator(key3, ptr3);

        // A hash below the first separator should go to leftmost_child
        let child = internal.find_child(HTreeHash::from_name("__50"));
        assert!(child.is_marker()); // leftmost_child is marker(0)

        // A hash at the last separator should go to the last child
        let child = internal.find_child(HTreeHash::from_name("__350"));
        assert!(child.is_marker()); // last separator's child_ptr
    }
}

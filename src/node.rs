use core::{fmt, mem, ops, slice};
use endian_num::Le;

use crate::{BlockLevel, BlockList, BlockPtr, BlockTrait, RecordRaw, BLOCK_SIZE, RECORD_LEVEL};

#[derive(Clone, Copy, Debug, Default)]
#[repr(C, packed)]
pub struct AclEntry {
    pub tag: u8,
    pub id: Le<u32>,
    pub perms: Le<u16>,
}

pub const ACL_ENTRIES_PER_BLOCK: usize = BLOCK_SIZE as usize / mem::size_of::<AclEntry>();
pub const ACL_TAG_USER: u8 = 1;
pub const ACL_TAG_GROUP: u8 = 2;
pub const ACL_TAG_OTHER: u8 = 3;
pub const ACL_TAG_MASK: u8 = 4;

#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct AclList {
    pub entries: [AclEntry; ACL_ENTRIES_PER_BLOCK],
}

impl Default for AclList {
    fn default() -> Self {
        Self {
            entries: [AclEntry::default(); ACL_ENTRIES_PER_BLOCK],
        }
    }
}

unsafe impl BlockTrait for AclList {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self::default())
        } else {
            None
        }
    }
}

impl ops::Deref for AclList {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(self as *const AclList as *const u8, mem::size_of::<AclList>())
                as &[u8]
        }
    }
}

impl ops::DerefMut for AclList {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(self as *mut AclList as *mut u8, mem::size_of::<AclList>())
                as &mut [u8]
        }
    }
}

bitflags::bitflags! {
    /// Flags for a node.
    pub struct NodeFlags: u32 {
        /// The node data is stored inline in the node itself.
        const INLINE_DATA = 0x1;
    }
}

/// An index into a [`Node`]'s block table.
pub enum NodeLevel {
    L0(usize),
    L1(usize, usize),
    L2(usize, usize, usize),
    L3(usize, usize, usize, usize),
    L4(usize, usize, usize, usize, usize),
}

impl NodeLevel {
    // Warning: this uses constant record offsets, make sure to sync with Node

    /// Return the [`NodeLevel`] of the record with the given index.
    /// - the first 56 are level 0,
    /// - the next 36*128 are level 1,
    /// - ...and so on.
    pub fn new(mut record_offset: u64) -> Option<Self> {
        // 1 << 7 = 128, this is the number of entries in a BlockList (4096 / 32)
        const SHIFT: u64 = 7;
        const NUM: u64 = 1 << SHIFT;
        const MASK: u64 = NUM - 1;

        const L0: u64 = 56;
        if record_offset < L0 {
            return Some(Self::L0((record_offset & MASK) as usize));
        } else {
            record_offset -= L0;
        }

        const L1: u64 = 36 * NUM;
        if record_offset < L1 {
            return Some(Self::L1(
                ((record_offset >> SHIFT) & MASK) as usize,
                (record_offset & MASK) as usize,
            ));
        } else {
            record_offset -= L1;
        }

        const L2: u64 = 18 * NUM * NUM;
        if record_offset < L2 {
            return Some(Self::L2(
                ((record_offset >> (2 * SHIFT)) & MASK) as usize,
                ((record_offset >> SHIFT) & MASK) as usize,
                (record_offset & MASK) as usize,
            ));
        } else {
            record_offset -= L2;
        }

        const L3: u64 = 10 * NUM * NUM * NUM;
        if record_offset < L3 {
            return Some(Self::L3(
                ((record_offset >> (3 * SHIFT)) & MASK) as usize,
                ((record_offset >> (2 * SHIFT)) & MASK) as usize,
                ((record_offset >> SHIFT) & MASK) as usize,
                (record_offset & MASK) as usize,
            ));
        } else {
            record_offset -= L3;
        }

        const L4: u64 = 4 * NUM * NUM * NUM * NUM;
        if record_offset < L4 {
            Some(Self::L4(
                ((record_offset >> (4 * SHIFT)) & MASK) as usize,
                ((record_offset >> (3 * SHIFT)) & MASK) as usize,
                ((record_offset >> (2 * SHIFT)) & MASK) as usize,
                ((record_offset >> SHIFT) & MASK) as usize,
                (record_offset & MASK) as usize,
            ))
        } else {
            None
        }
    }
}

type BlockListL1 = BlockList<RecordRaw>;
type BlockListL2 = BlockList<BlockListL1>;
type BlockListL3 = BlockList<BlockListL2>;
type BlockListL4 = BlockList<BlockListL3>;

/// Data pointers for a node, organized by level.
///
/// This struct allows for efficient access to file data, supporting sparse files and large files.
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct NodeLevelData {
    /// The first 56 blocks of this file.
    pub level0: [BlockPtr<RecordRaw>; 56],

    /// The next 36 * 128 blocks of this file.
    pub level1: [BlockPtr<BlockListL1>; 36],

    /// The next 18 * 128^2 blocks.
    pub level2: [BlockPtr<BlockListL2>; 18],

    /// The next 10 * 128^3 blocks.
    pub level3: [BlockPtr<BlockListL3>; 10],

    /// The next 4 * 128^4 blocks.
    pub level4: [BlockPtr<BlockListL4>; 4],
}

impl Default for NodeLevelData {
    fn default() -> Self {
        Self {
            level0: [BlockPtr::default(); 56],
            level1: [BlockPtr::default(); 36],
            level2: [BlockPtr::default(); 18],
            level3: [BlockPtr::default(); 10],
            level4: [BlockPtr::default(); 4],
        }
    }
}

/// A file/folder node.
///
/// This struct represents an inode in the filesystem, containing metadata like permissions,
/// timestamps, and pointers to data blocks.
#[derive(Clone)]
#[repr(C, packed)]
pub struct Node {
    /// This node's type & permissions.
    pub mode: Le<u16>,

    /// The uid that owns this file
    pub uid: Le<u32>,

    /// The gid that owns this file
    pub gid: Le<u32>,

    /// The number of hard links to this file
    pub links: Le<u32>,

    /// The length of this file, in bytes
    pub size: Le<u64>,
    /// The disk usage of this file, in blocks
    pub blocks: Le<u64>,

    /// Creation time
    pub ctime: Le<u64>,
    pub ctime_nsec: Le<u32>,

    /// Modification time
    pub mtime: Le<u64>,
    pub mtime_nsec: Le<u32>,

    /// Access time
    pub atime: Le<u64>,
    pub atime_nsec: Le<u32>,

    /// Record level
    pub record_level: Le<u32>,

    /// Compression hint (0 = None, 1 = LZ4, 2 = ZSTD)
    pub compression_hint: u8,

    /// Flags
    pub flags: Le<u32>,

    /// Padding.
    /// BLOCK_SIZE = 4096.
    /// Header = 75 bytes.
    /// AclPtr = 32 bytes.
    /// NodeLevelData = 124 * 32 = 3968 bytes.
    /// Total used = 75 + 32 + 3968 = 4075 bytes.
    /// Padding = 4096 - 4075 = 21 bytes.
    pub padding: [u8; 21],

    /// Pointer to the ACL list
    pub acl_ptr: BlockPtr<AclList>,

    /// Level data, should not be used directly so inline data can be supported
    pub(crate) level_data: NodeLevelData,
}

unsafe impl BlockTrait for Node {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self::default())
        } else {
            None
        }
    }
}

impl Default for Node {
    fn default() -> Self {
        Self {
            mode: 0.into(),
            uid: 0.into(),
            gid: 0.into(),
            links: 0.into(),
            size: 0.into(),
            // This node counts as a block
            blocks: 1.into(),
            ctime: 0.into(),
            ctime_nsec: 0.into(),
            mtime: 0.into(),
            mtime_nsec: 0.into(),
            atime: 0.into(),
            atime_nsec: 0.into(),
            record_level: 0.into(),
            compression_hint: 0,
            flags: 0.into(),
            padding: [0; 21],
            acl_ptr: BlockPtr::default(),
            level_data: NodeLevelData::default(),
        }
    }
}

impl Node {
    pub const MODE_TYPE: u16 = 0xF000;
    pub const MODE_FILE: u16 = 0x8000;
    pub const MODE_DIR: u16 = 0x4000;
    pub const MODE_SYMLINK: u16 = 0xA000;
    pub const MODE_SOCK: u16 = 0xC000;

    /// Mask for node permission bits
    pub const MODE_PERM: u16 = 0x0FFF;
    pub const MODE_EXEC: u16 = 0o1;
    pub const MODE_WRITE: u16 = 0o2;
    pub const MODE_READ: u16 = 0o4;

    /// Create a new, empty node with the given metadata
    pub fn new(mode: u16, uid: u32, gid: u32, ctime: u64, ctime_nsec: u32) -> Self {
        Self {
            mode: mode.into(),
            uid: uid.into(),
            gid: gid.into(),
            links: 0.into(),
            ctime: ctime.into(),
            ctime_nsec: ctime_nsec.into(),
            mtime: ctime.into(),
            mtime_nsec: ctime_nsec.into(),
            atime: ctime.into(),
            atime_nsec: ctime_nsec.into(),
            record_level: if mode & Self::MODE_TYPE == Self::MODE_FILE {
                // Files take on record level
                RECORD_LEVEL as u32
            } else {
                // Folders do not
                0
            }
            .into(),
            flags: if mode & Self::MODE_TYPE == Self::MODE_DIR {
                // Directories must not use inline data (until h-tree supports it)
                NodeFlags::empty()
            } else {
                NodeFlags::INLINE_DATA
            }
            .bits()
            .into(),
            ..Default::default()
        }
    }

    /// Get the node's mode (type and permissions).
    ///
    /// The mode contains:
    /// - 4 most significant bits: node type (file, dir, symlink, etc.)
    /// - 12 least significant bits: permissions (rwx for user, group, other)
    pub fn mode(&self) -> u16 {
        self.mode.to_ne()
    }

    /// The uid that owns this file
    pub fn uid(&self) -> u32 {
        self.uid.to_ne()
    }

    /// The gid that owns this file
    pub fn gid(&self) -> u32 {
        self.gid.to_ne()
    }

    /// The number of links to this file
    /// (directory entries, symlinks, etc)
    pub fn links(&self) -> u32 {
        self.links.to_ne()
    }

    /// The length of this file, in bytes.
    pub fn size(&self) -> u64 {
        self.size.to_ne()
    }

    /// The disk usage of this file, in blocks.
    pub fn blocks(&self) -> u64 {
        self.blocks.to_ne()
    }

    pub fn ctime(&self) -> (u64, u32) {
        (self.ctime.to_ne(), self.ctime_nsec.to_ne())
    }

    pub fn mtime(&self) -> (u64, u32) {
        (self.mtime.to_ne(), self.mtime_nsec.to_ne())
    }

    pub fn atime(&self) -> (u64, u32) {
        (self.atime.to_ne(), self.atime_nsec.to_ne())
    }

    pub fn record_level(&self) -> BlockLevel {
        BlockLevel(self.record_level.to_ne() as usize)
    }

    pub fn flags(&self) -> NodeFlags {
        NodeFlags::from_bits_retain(self.flags.to_ne())
    }

    pub fn set_mode(&mut self, mode: u16) {
        self.mode = mode.into();
    }

    pub fn set_uid(&mut self, uid: u32) {
        self.uid = uid.into();
    }

    pub fn set_gid(&mut self, gid: u32) {
        self.gid = gid.into();
    }

    pub fn set_links(&mut self, links: u32) {
        self.links = links.into();
    }

    pub fn set_size(&mut self, size: u64) {
        self.size = size.into();
    }

    pub fn set_blocks(&mut self, blocks: u64) {
        self.blocks = blocks.into();
    }

    pub fn set_mtime(&mut self, mtime: u64, mtime_nsec: u32) {
        self.mtime = mtime.into();
        self.mtime_nsec = mtime_nsec.into();
    }

    pub fn set_atime(&mut self, atime: u64, atime_nsec: u32) {
        self.atime = atime.into();
        self.atime_nsec = atime_nsec.into();
    }

    pub fn set_flags(&mut self, flags: NodeFlags) {
        self.flags = flags.bits().into();
    }

    pub fn set_compression_hint(&mut self, hint: u8) {
        self.compression_hint = hint;
    }

    pub fn compression_hint(&self) -> u8 {
        self.compression_hint
    }

    pub fn has_inline_data(&self) -> bool {
        self.flags().contains(NodeFlags::INLINE_DATA)
    }

    pub fn inline_data(&self) -> Option<&[u8]> {
        if self.has_inline_data() {
            Some(unsafe {
                slice::from_raw_parts(
                    &self.level_data as *const NodeLevelData as *const u8,
                    mem::size_of::<NodeLevelData>(),
                )
            })
        } else {
            None
        }
    }

    pub fn inline_data_mut(&mut self) -> Option<&mut [u8]> {
        if self.has_inline_data() {
            Some(unsafe {
                slice::from_raw_parts_mut(
                    &mut self.level_data as *mut NodeLevelData as *mut u8,
                    mem::size_of::<NodeLevelData>(),
                )
            })
        } else {
            None
        }
    }

    pub fn level_data(&self) -> Option<&NodeLevelData> {
        if !self.has_inline_data() {
            Some(&self.level_data)
        } else {
            None
        }
    }

    pub fn level_data_mut(&mut self) -> Option<&mut NodeLevelData> {
        if !self.has_inline_data() {
            Some(&mut self.level_data)
        } else {
            None
        }
    }

    pub fn is_dir(&self) -> bool {
        self.mode() & Self::MODE_TYPE == Self::MODE_DIR
    }

    pub fn is_file(&self) -> bool {
        self.mode() & Self::MODE_TYPE == Self::MODE_FILE
    }

    pub fn is_symlink(&self) -> bool {
        self.mode() & Self::MODE_TYPE == Self::MODE_SYMLINK
    }

    pub fn is_sock(&self) -> bool {
        self.mode() & Self::MODE_SOCK == Self::MODE_SOCK
    }

    /// Tests if UID is the owner of that file, only true when uid=0 or when the UID stored in metadata is equal to the UID you supply
    pub fn owner(&self, uid: u32) -> bool {
        uid == 0 || self.uid() == uid
    }

    /// Tests if the current user has enough permissions to view the file, op is the operation,
    /// like read and write, these modes are MODE_EXEC, MODE_READ, and MODE_WRITE
    pub fn permission(&self, uid: u32, gid: u32, op: u16, acl: Option<&AclList>) -> bool {
        if uid == 0 {
            return true;
        }

        if let Some(acl_list) = acl {
            let mut found = false;
            let mut acl_perm = 0;
            for entry in acl_list.entries.iter() {
                if entry.tag == 0 { break; }
                if entry.tag == ACL_TAG_USER && entry.id.to_ne() == uid {
                    acl_perm = entry.perms.to_ne();
                    found = true;
                    break;
                }
                // Group logic requires checking all groups.
                // Simplified: Check if gid matches.
                if entry.tag == ACL_TAG_GROUP && entry.id.to_ne() == gid {
                     acl_perm |= entry.perms.to_ne();
                     found = true;
                }
            }
            if found {
                return acl_perm & op == op;
            }
        }
        
        let mut perm = self.mode() & 0o7;
        if self.uid() == uid {
            perm |= (self.mode() >> 6) & 0o7;
        }
        if self.gid() == gid || gid == 0 {
            perm |= (self.mode() >> 3) & 0o7;
        }
        perm & op == op
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mode = self.mode;
        let uid = self.uid;
        let gid = self.gid;
        let links = self.links;
        let size = self.size;
        let blocks = self.blocks;
        let ctime = self.ctime;
        let ctime_nsec = self.ctime_nsec;
        let mtime = self.mtime;
        let mtime_nsec = self.mtime_nsec;
        let atime = self.atime;
        let atime_nsec = self.atime_nsec;
        f.debug_struct("Node")
            .field("mode", &mode)
            .field("uid", &uid)
            .field("gid", &gid)
            .field("links", &links)
            .field("size", &size)
            .field("blocks", &blocks)
            .field("ctime", &ctime)
            .field("ctime_nsec", &ctime_nsec)
            .field("mtime", &mtime)
            .field("mtime_nsec", &mtime_nsec)
            .field("atime", &atime)
            .field("atime_nsec", &atime_nsec)
            //TODO: level0/1/2/3
            .finish()
    }
}

impl ops::Deref for Node {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(self as *const Node as *const u8, mem::size_of::<Node>())
                as &[u8]
        }
    }
}

impl ops::DerefMut for Node {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(self as *mut Node as *mut u8, mem::size_of::<Node>())
                as &mut [u8]
        }
    }
}

#[test]
fn node_size_test() {
    assert_eq!(mem::size_of::<Node>(), crate::BLOCK_SIZE as usize);
}

#[test]
fn node_inline_data_test() {
    let mut node = Node::default();
    assert!(!node.has_inline_data());
    assert!(node.inline_data().is_none());
    assert!(node.inline_data_mut().is_none());
    assert!(node.level_data().is_some());
    assert!(node.level_data_mut().is_some());

    node.set_flags(NodeFlags::INLINE_DATA);
    assert!(node.has_inline_data());
    assert!(node.level_data().is_none());
    assert!(node.level_data_mut().is_none());

    let node_addr = &node as *const Node as usize;
    // Header size + padding + acl_ptr size
    let meta_size = 75 + 21 + 32; 
    {
        let inline_data = node.inline_data().unwrap();
        let inline_data_addr = inline_data.as_ptr() as usize;
        assert_eq!(node_addr + meta_size, inline_data_addr);
        assert_eq!(inline_data.len(), (crate::BLOCK_SIZE as usize) - meta_size);
    }
    {
        let inline_data = node.inline_data_mut().unwrap();
        let inline_data_addr = inline_data.as_ptr() as usize;
        assert_eq!(node_addr + meta_size, inline_data_addr);
        assert_eq!(inline_data.len(), (crate::BLOCK_SIZE as usize) - meta_size);
    }
}

#[cfg(kani)]
#[kani::proof]
fn check_node_level() {
    let offset = kani::any();
    NodeLevel::new(offset);
}

#[cfg(kani)]
#[kani::proof]
fn check_node_perms() {
    let mode = 0o750;

    let uid = kani::any();
    let gid = kani::any();

    let ctime = kani::any();
    let ctime_nsec = kani::any();

    let node = Node::new(mode, uid, gid, ctime, ctime_nsec);

    let root_uid = 0;
    let root_gid = 0;

    let other_uid = kani::any();
    kani::assume(other_uid != uid);
    kani::assume(other_uid != root_uid);
    let other_gid = kani::any();
    kani::assume(other_gid != gid);
    kani::assume(other_gid != root_gid);

    assert!(node.owner(uid));
    assert!(node.permission(uid, gid, 0o7, None));
    assert!(node.permission(uid, gid, 0o5, None));
    assert!(node.permission(uid, other_gid, 0o7, None));
    assert!(node.permission(uid, other_gid, 0o5, None));
    assert!(!node.permission(other_uid, gid, 0o7, None));
    assert!(node.permission(other_uid, gid, 0o5, None));

    assert!(node.owner(root_uid));
    assert!(node.permission(root_uid, root_gid, 0o7, None));
    assert!(node.permission(root_uid, root_gid, 0o5, None));
    assert!(node.permission(root_uid, other_gid, 0o7, None));
    assert!(node.permission(root_uid, other_gid, 0o5, None));
    assert!(!node.permission(other_uid, root_gid, 0o7, None));
    assert!(node.permission(other_uid, root_gid, 0o5, None));

    assert!(!node.owner(other_uid));
    assert!(!node.permission(other_uid, other_gid, 0o7, None));
    assert!(!node.permission(other_uid, other_gid, 0o5, None));
}

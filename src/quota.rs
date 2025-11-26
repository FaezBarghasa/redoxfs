use core::{mem, ops, slice};
use endian_num::Le;

use crate::{BlockLevel, BlockPtr, BlockTrait, Tree, BLOCK_SIZE};

#[derive(Clone, Copy, Default, Debug)]
#[repr(C, packed)]
pub struct QuotaEntry {
    pub block_usage: Le<u64>,
    pub block_limit: Le<u64>,
    pub inode_usage: Le<u64>,
    pub inode_limit: Le<u64>,
}

pub const QUOTA_ENTRIES_PER_BLOCK: usize = BLOCK_SIZE as usize / mem::size_of::<QuotaEntry>();

#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct QuotaList {
    pub entries: [QuotaEntry; QUOTA_ENTRIES_PER_BLOCK],
}

impl Default for QuotaList {
    fn default() -> Self {
        Self {
            entries: [QuotaEntry::default(); QUOTA_ENTRIES_PER_BLOCK],
        }
    }
}

unsafe impl BlockTrait for QuotaList {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self::default())
        } else {
            None
        }
    }
}

impl ops::Deref for QuotaList {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(self as *const QuotaList as *const u8, mem::size_of::<QuotaList>())
                as &[u8]
        }
    }
}

impl ops::DerefMut for QuotaList {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(self as *mut QuotaList as *mut u8, mem::size_of::<QuotaList>())
                as &mut [u8]
        }
    }
}

#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct QuotaRoot {
    pub user_tree: BlockPtr<Tree>,
    pub group_tree: BlockPtr<Tree>,
    padding: [u8; BLOCK_SIZE as usize - 64],
}

impl Default for QuotaRoot {
    fn default() -> Self {
        Self {
            user_tree: BlockPtr::default(),
            group_tree: BlockPtr::default(),
            padding: [0; BLOCK_SIZE as usize - 64],
        }
    }
}

unsafe impl BlockTrait for QuotaRoot {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self::default())
        } else {
            None
        }
    }
}

impl ops::Deref for QuotaRoot {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(self as *const QuotaRoot as *const u8, mem::size_of::<QuotaRoot>())
                as &[u8]
        }
    }
}

impl ops::DerefMut for QuotaRoot {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(self as *mut QuotaRoot as *mut u8, mem::size_of::<QuotaRoot>())
                as &mut [u8]
        }
    }
}

use core::{mem, ops, slice};
use endian_num::Le;

use crate::{BlockLevel, BlockTrait, BLOCK_SIZE};

#[derive(Clone, Copy, Default, Debug)]
#[repr(C, packed)]
pub struct RefcountEntry {
    pub block_index: Le<u64>,
    pub ref_count: Le<u64>,
}

pub const REFCOUNT_ENTRIES_PER_BLOCK: usize = BLOCK_SIZE as usize / mem::size_of::<RefcountEntry>();

#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct RefcountList {
    pub entries: [RefcountEntry; REFCOUNT_ENTRIES_PER_BLOCK],
}

impl Default for RefcountList {
    fn default() -> Self {
        Self {
            entries: [RefcountEntry::default(); REFCOUNT_ENTRIES_PER_BLOCK],
        }
    }
}

unsafe impl BlockTrait for RefcountList {
    fn empty(level: BlockLevel) -> Option<Self> {
        if level.0 == 0 {
            Some(Self::default())
        } else {
            None
        }
    }
}

impl ops::Deref for RefcountList {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self as *const RefcountList as *const u8,
                mem::size_of::<RefcountList>(),
            ) as &[u8]
        }
    }
}

impl ops::DerefMut for RefcountList {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(
                self as *mut RefcountList as *mut u8,
                mem::size_of::<RefcountList>(),
            ) as &mut [u8]
        }
    }
}

// src/driver/nvme_rs.rs
use core::ptr;
use core::sync::atomic::{AtomicU16, Ordering};
use core::mem;
use syscall::error::{Result, EIO};

#[repr(C)]
pub struct NvmeRegs {
    pub cap: u64,
    pub vs: u32,
    pub intms: u32,
    pub intmc: u32,
    pub cc: u32,
    pub csts: u32,
    pub nssr: u32,
    pub aqa: u32,
    pub asq: u64,
    pub acq: u64,
    pub cmbloc: u32,
    pub cmbsz: u32,
}

#[repr(align(4096))]
pub struct Aligned<T>(pub T);

#[repr(C, align(64))]
#[derive(Clone, Copy)]
pub struct SqEntry {
    pub command_dword_0: u32,
    pub namespace_id: u32,
    pub reserved: [u64; 2],
    pub metadata_pointer: u64,
    pub data_pointer_prp1: u64,
    pub data_pointer_prp2: u64,
    pub command_dword_10: u32,
    pub command_dword_11: u32,
    pub command_dword_12: u32,
    pub command_dword_13: u32,
    pub command_dword_14: u32,
    pub command_dword_15: u32,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct CqEntry {
    pub command_specific: u32,
    pub reserved: u32,
    pub sq_head: u16,
    pub sq_id: u16,
    pub command_id: u16,
    pub status: u16,
}

pub struct NvmeDriver {
    pub regs_base: *mut NvmeRegs,
    pub admin_sq: Aligned<[SqEntry; 64]>,
    pub admin_cq: Aligned<[CqEntry; 64]>,
    pub command_id_counter: AtomicU16,
}

impl NvmeDriver {
    pub fn new(mmio_addr: usize) -> Result<Self> {
        Ok(NvmeDriver {
            regs_base: mmio_addr as *mut NvmeRegs,
            admin_sq: Aligned([SqEntry::default(); 64]),
            admin_cq: Aligned([CqEntry::default(); 64]),
            command_id_counter: AtomicU16::new(1),
        })
    }

    pub fn ring_doorbell(&self, sq_id: u16, new_head: u16) {
        let offset = 0x1000 + (sq_id as usize) * 8;
        unsafe {
            ptr::write_volatile(
                (self.regs_base as *mut u8).add(offset) as *mut u32,
                new_head as u32
            );
        }
    }

    pub fn poll_completion(&self) -> Option<CqEntry> {
        let cq_entry_index = 0;
        let cq_entry = unsafe { ptr::read_volatile(&self.admin_cq.0[cq_entry_index]) };

        if (cq_entry.status & 1) != 0 {
            Some(cq_entry)
        } else {
            None
        }
    }
}

impl Default for SqEntry { fn default() -> Self { unsafe { mem::zeroed() } } }
impl Default for CqEntry { fn default() -> Self { unsafe { mem::zeroed() } } }
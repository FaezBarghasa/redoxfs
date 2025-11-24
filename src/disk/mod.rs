// src/disk/mod.rs
use syscall::error::{Result, EIO};

#[cfg(feature = "std")]
pub use self::cache::DiskCache;
#[cfg(feature = "std")]
pub use self::file::DiskFile;
#[cfg(feature = "std")]
pub use self::io::DiskIo;
#[cfg(feature = "std")]
pub use self::memory::DiskMemory;
#[cfg(feature = "std")]
pub use self::sparse::DiskSparse;

#[cfg(feature = "std")]
mod cache;
#[cfg(feature = "std")]
mod file;
#[cfg(feature = "std")]
mod io;
#[cfg(feature = "std")]
mod memory;
#[cfg(feature = "std")]
mod sparse;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MediaType {
    Unknown,
    HDD,        // Rotational media (high seek time)
    SSD,        // Solid state (low seek time, supports TRIM)
    NVMe,       // High performance SSD (very low latency, massive parallelism)
    SDCard,     // Flash storage (often slow random write, erase block management needed)
}

/// A disk
pub trait Disk {
    /// Read blocks from disk
    ///
    /// # Safety
    /// Unsafe to discourage use, use filesystem wrappers instead
    unsafe fn read_at(&mut self, block: u64, buffer: &mut [u8]) -> Result<usize>;

    /// Write blocks from disk
    ///
    /// # Safety
    /// Unsafe to discourage use, use filesystem wrappers instead
    unsafe fn write_at(&mut self, block: u64, buffer: &[u8]) -> Result<usize>;

    /// Write blocks from disk, returning which disk(s) failed (if any).
    /// Used by DiskMirror for fault tolerance tracking.
    unsafe fn write_at_mirrored(&mut self, block: u64, buffer: &[u8]) -> Result<u8> {
        // Default implementation just calls write_at and returns simple success/fail
        match self.write_at(block, buffer) {
            Ok(_) => Ok(0),
            Err(_) => Ok(1), // Assume single disk failed
        }
    }

    /// Get size of disk in bytes
    fn size(&mut self) -> Result<u64>;

    /// Get the media type of the disk
    fn media_type(&self) -> MediaType {
        MediaType::Unknown
    }

    /// Send a TRIM/DISCARD command to the device (for SSD/NVMe/SD)
    /// Default implementation does nothing.
    fn trim(&mut self, _block: u64, _count: u64) -> Result<()> {
        Ok(())
    }
}

pub struct DiskMirror<D: Disk> {
    pub disks: [D; 2],
    pub active_mask: u8, // e.g., 0b11 for both active
}

impl<D: Disk> Disk for DiskMirror<D> {
    unsafe fn read_at(&mut self, block: u64, buffer: &mut [u8]) -> Result<usize> {
        // Try disk 0, then disk 1
        if self.active_mask & 1 != 0 {
            if let Ok(sz) = self.disks[0].read_at(block, buffer) { return Ok(sz); }
        }
        if self.active_mask & 2 != 0 {
            return self.disks[1].read_at(block, buffer);
        }
        Err(Error::new(EIO))
    }

    unsafe fn write_at(&mut self, block: u64, buffer: &[u8]) -> Result<usize> {
        // Write to all active disks. Fail if any fail (strict write).
        // This is for non-mirrored contexts or where we want strict consistency
        let mut success = false;
        if self.active_mask & 1 != 0 {
            self.disks[0].write_at(block, buffer)?;
            success = true;
        }
        if self.active_mask & 2 != 0 {
            self.disks[1].write_at(block, buffer)?;
            success = true;
        }
        if success {
            Ok(buffer.len())
        } else {
            Err(Error::new(EIO))
        }
    }

    unsafe fn write_at_mirrored(&mut self, block: u64, buffer: &[u8]) -> Result<u8> {
        let mut fail_mask = 0;
        // Try write to disk 0
        if self.active_mask & 1 != 0 {
            if self.disks[0].write_at(block, buffer).is_err() { fail_mask |= 1; }
        }
        // Try write to disk 1
        if self.active_mask & 2 != 0 {
            if self.disks[1].write_at(block, buffer).is_err() { fail_mask |= 2; }
        }

        if fail_mask == self.active_mask {
            // All active disks failed
            Err(Error::new(EIO))
        } else {
            Ok(fail_mask)
        }
    }

    fn size(&mut self) -> Result<u64> {
        self.disks[0].size() // Assume equal size
    }

    fn media_type(&self) -> MediaType {
        // Return the media type of the primary disk
        self.disks[0].media_type()
    }

    fn trim(&mut self, block: u64, count: u64) -> Result<()> {
        // TRIM both disks if possible
        if self.active_mask & 1 != 0 {
            let _ = self.disks[0].trim(block, count);
        }
        if self.active_mask & 2 != 0 {
            let _ = self.disks[1].trim(block, count);
        }
        Ok(())
    }
}

use syscall::error::Error;
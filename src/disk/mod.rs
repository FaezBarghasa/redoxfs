//! Generic disk traits and implementations
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

/// The type of media, which can be used for optimization
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MediaType {
    /// Unknown media type
    Unknown,
    /// Rotational media (high seek time)
    HDD,
    /// Solid state (low seek time, supports TRIM)
    SSD,
    /// High performance SSD (very low latency, massive parallelism)
    NVMe,
    /// Flash storage (often slow random write, erase block management needed)
    SDCard,
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
    /// The default implementation calls `write_at` and returns a failure if any write fails.
    /// A return value of `Ok(0)` means success. `Ok(1)` means the first disk failed, `Ok(2)` means the second failed, and `Ok(3)` means both failed.
    ///
    /// # Safety
    /// Unsafe to discourage use, use filesystem wrappers instead
    unsafe fn write_at_mirrored(&mut self, block: u64, buffer: &[u8]) -> Result<u8> {
        // Default implementation just calls write_at and returns simple success/fail
        match self.write_at(block, buffer) {
            Ok(_) => Ok(0),
            Err(_) => Ok(1), // Assume single disk failed
        }
    }

    /// Get size of disk in bytes
    fn size(&mut self) -> Result<u64>;

    /// Get the media type of the disk. The default is `Unknown`.
    fn media_type(&self) -> MediaType {
        MediaType::Unknown
    }

    /// Send a TRIM/DISCARD command to the device (for SSD/NVMe/SD)
    /// The default implementation does nothing.
    fn trim(&mut self, _block: u64, _count: u64) -> Result<()> {
        Ok(())
    }
}

/// A disk that mirrors across two disks
pub struct DiskMirror<D: Disk> {
    /// The two disks to mirror across
    pub disks: [D; 2],
    /// A bitmask of active disks.
    ///
    /// For example, `0b01` means only the first disk is active, `0b10` means only the second is active, and `0b11` means both are active.
    pub active_mask: u8,
}

impl<D: Disk> Disk for DiskMirror<D> {
    /// Read from the first active disk.
    ///
    /// # Safety
    /// Unsafe to discourage use, use filesystem wrappers instead
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

    /// Write to all active disks.
    ///
    /// # Safety
    /// Unsafe to discourage use, use filesystem wrappers instead
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

    /// Write to all active disks, returning a bitmask of failed disks.
    ///
    /// # Safety
    /// Unsafe to discourage use, use filesystem wrappers instead
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

    /// Get the size of the first disk. It is assumed that both disks have the same size.
    fn size(&mut self) -> Result<u64> {
        self.disks[0].size() // Assume equal size
    }

    /// Get the media type of the first disk.
    fn media_type(&self) -> MediaType {
        // Return the media type of the primary disk
        self.disks[0].media_type()
    }

    /// Trim both disks.
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

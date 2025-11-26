use syscall::error::{Error, Result, EIO};

use super::{Disk, MediaType};

/// A `DiskMirror` provides a mirrored disk configuration, where data is written to two underlying
/// disks simultaneously. This provides redundancy and fault tolerance. If one disk fails, data
/// can still be read from the other.
pub struct DiskMirror<D: Disk> {
    /// The two disks to mirror across.
    pub disks: [D; 2],
    /// A bitmask indicating which disks are active.
    ///
    /// For example, `0b01` means only the first disk is active, `0b10` means only the second is
    /// active, and `0b11` means both are active.
    pub active_mask: u8,
}

impl<D: Disk> Disk for DiskMirror<D> {
    /// Reads from the first available active disk.
    ///
    /// This implementation tries to read from the first disk. If that fails, it tries the second
    /// disk. This allows the system to continue functioning even if one of the disks has failed.
    ///
    /// # Safety
    ///
    /// This method is unsafe for the same reasons as `Disk::read_at`.
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

    /// Writes to all active disks.
    ///
    /// This method ensures that data is written to all active disks in the mirror. If any of the
    /// writes fail, the entire operation fails. This provides strict consistency.
    ///
    /// # Safety
    ///
    /// This method is unsafe for the same reasons as `Disk::write_at`.
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

    /// Writes to all active disks and returns a bitmask of any disks that failed.
    ///
    /// This method is used for mirrored writes where you want to track which disks have failed.
    /// Unlike `write_at`, this method does not fail if one of the writes fails. Instead, it
    /// returns a bitmask indicating which disk(s) failed.
    ///
    /// # Safety
    ///
    /// This method is unsafe for the same reasons as `Disk::write_at`.
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

    /// Returns the size of the first disk. It is assumed that both disks have the same size.
    fn size(&mut self) -> Result<u64> {
        self.disks[0].size() // Assume equal size
    }

    /// Returns the media type of the first disk.
    fn media_type(&self) -> MediaType {
        // Return the media type of the primary disk
        self.disks[0].media_type()
    }

    /// Sends a TRIM command to both disks.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::disk::DiskMemory;

    #[test]
    fn test_mirror_write_read() {
        let d1 = DiskMemory::new(4096 * 10);
        let d2 = DiskMemory::new(4096 * 10);
        let mut mirror = DiskMirror {
            disks: [d1, d2],
            active_mask: 3,
        };

        let data = [1u8; 4096];
        unsafe {
            mirror.write_at(0, &data).unwrap();
        }

        let mut buf = [0u8; 4096];
        unsafe {
            mirror.read_at(0, &mut buf).unwrap();
        }
        assert_eq!(buf, data);
    }

    #[test]
    fn test_mirror_failover() {
        let d1 = DiskMemory::new(4096 * 10);
        let d2 = DiskMemory::new(4096 * 10);
        let mut mirror = DiskMirror {
            disks: [d1, d2],
            active_mask: 3,
        };

        let data = [2u8; 4096];
        unsafe {
            mirror.write_at(1, &data).unwrap();
        }

        // Simulate disk 1 failure by masking it out
        mirror.active_mask = 2; // Only disk 2 active

        let mut buf = [0u8; 4096];
        unsafe {
            mirror.read_at(1, &mut buf).unwrap();
        }
        assert_eq!(buf, data);
    }
}

//! # Disk
//!
//! The `disk` module provides a generic interface for block devices, which are simply called
//! "disks" here. The main component is the `Disk` trait, which abstracts the operations that can
//! be performed on a disk, such as reading and writing blocks of data.
//!
//! This module also provides several implementations of the `Disk` trait:
//!
//! - `DiskCache`: A wrapper that adds a layer of caching to a disk, improving performance by
//!   reducing the number of physical disk accesses.
//! - `DiskFile`: An implementation that uses a file as the backing storage for the disk. This is
//!   useful for creating disk images and for testing purposes.
//! - `DiskIo`: A wrapper that uses standard I/O instead of memory maps.
//! - `DiskMemory`: An in-memory implementation of a disk, useful for testing where you need a
//!   fast, temporary disk.
//! - `DiskSparse`: An implementation for sparse files, which are files that can have "holes" in
//!   them, saving space on the storage medium.
//! - `DiskMirror`: A wrapper that mirrors data across two disks, providing redundancy and fault
//!   tolerance.

use syscall::error::{Error, Result, EIO};

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
pub use self::mirror::DiskMirror;

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
mod mirror;

/// The type of media, which can be used for optimization.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MediaType {
    /// The media type is unknown.
    Unknown,
    /// Rotational media, like a Hard Disk Drive (HDD). These have high seek times.
    HDD,
    /// Solid State Drive (SSD). These have low seek times and may support TRIM.
    SSD,
    /// Non-Volatile Memory Express (NVMe) drive. A very high-performance SSD.
    NVMe,
    /// Secure Digital (SD) card. Often has slow random write performance and requires erase block
    /// management.
    SDCard,
}

/// Hint for the type of block being read.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BlockTypeHint {
    Metadata,
    Data,
}

/// The `Disk` trait provides a generic interface for a block device.
pub trait Disk {
    /// Reads a block from the disk.
    ///
    /// # Parameters
    ///
    /// - `block`: The block number to read from.
    /// - `buffer`: The buffer to read the data into. The length of the buffer determines how many
    ///   bytes to read.
    ///
    /// # Returns
    ///
    /// Returns the number of bytes read.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it provides direct, low-level access to the disk. Incorrect
    /// use, such as reading from an invalid block, can lead to data corruption or other errors.
    /// It is recommended to use higher-level filesystem wrappers instead.
    unsafe fn read_at(&mut self, block: u64, buffer: &mut [u8]) -> Result<usize>;

    /// Reads a block from the disk with a type hint.
    ///
    /// The default implementation ignores the hint and calls `read_at`.
    ///
    /// # Parameters
    ///
    /// - `block`: The block number to read from.
    /// - `buffer`: The buffer to read the data into.
    /// - `hint`: The type of block being read (Metadata or Data).
    unsafe fn read_at_with_hint(&mut self, block: u64, buffer: &mut [u8], _hint: BlockTypeHint) -> Result<usize> {
        self.read_at(block, buffer)
    }

    /// Writes a block to the disk.
    ///
    /// # Parameters
    ///
    /// - `block`: The block number to write to.
    /// - `buffer`: The buffer containing the data to write.
    ///
    /// # Returns
    ///
    /// Returns the number of bytes written.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it provides direct, low-level access to the disk. Incorrect
    /// use, such as writing to a wrong block, can lead to data corruption or other errors.
    /// It is recommended to use higher-level filesystem wrappers instead.
    unsafe fn write_at(&mut self, block: u64, buffer: &[u8]) -> Result<usize>;

    /// Writes a block to the disk in a mirrored configuration, returning which disk(s) failed,
    /// if any. This is used by `DiskMirror` for fault tolerance tracking.
    ///
    /// The default implementation calls `write_at` and returns a failure if the write fails.
    /// A return value of `Ok(0)` means success. `Ok(1)` means the first disk failed, `Ok(2)`
    /// means the second failed, and `Ok(3)` means both failed.
    ///
    /// # Parameters
    ///
    /// - `block`: The block number to write to.
    /// - `buffer`: The buffer containing the data to write.
    ///
    /// # Returns
    ///
    /// A `Result` containing a bitmask of the disks that failed.
    ///
    /// # Safety
    ///
    /// This method is unsafe for the same reasons as `write_at`. It provides low-level disk
    /// access and should be used with caution.
    unsafe fn write_at_mirrored(&mut self, block: u64, buffer: &[u8]) -> Result<u8> {
        // Default implementation just calls write_at and returns simple success/fail
        match self.write_at(block, buffer) {
            Ok(_) => Ok(0),
            Err(_) => Ok(1), // Assume single disk failed
        }
    }

    /// Returns the size of the disk in bytes.
    fn size(&mut self) -> Result<u64>;

    /// Returns the media type of the disk.
    ///
    /// The default implementation returns `MediaType::Unknown`.
    fn media_type(&self) -> MediaType {
        MediaType::Unknown
    }

    /// Sends a TRIM/DISCARD command to the device. This is a hint to the underlying storage
    /// that a range of blocks is no longer in use and can be erased. This is mainly used by
    /// SSDs to improve performance.
    ///
    /// The default implementation does nothing.
    ///
    /// # Parameters
    ///
    /// - `block`: The starting block number to trim.
    /// - `count`: The number of blocks to trim.
    fn trim(&mut self, _block: u64, _count: u64) -> Result<()> {
        Ok(())
    }
}

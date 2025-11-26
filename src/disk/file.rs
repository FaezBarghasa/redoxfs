//! A disk implemented by a file
use std::fs::{File, OpenOptions};
use std::io::{Seek, SeekFrom};
use std::os::unix::fs::FileExt;
use std::path::Path;

use syscall::error::{Error, Result, EIO};

use crate::disk::{Disk, MediaType}; // Import MediaType
use crate::BLOCK_SIZE;

/// A disk implemented by a file.
pub struct DiskFile {
    /// The file.
    pub file: File,
    /// The media type, which can be overriden.
    pub media_type: MediaType,
}

// TODO: move this to a common module, maybe even a library
trait ResultExt<T> {
    fn or_eio(self) -> Result<T>;
}

impl<T, E> ResultExt<T> for std::result::Result<T, E>
where
    E: std::fmt::Debug,
{
    fn or_eio(self) -> Result<T> {
        self.map_err(|_err| Error::new(EIO))
    }
}

impl DiskFile {
    /// Open a disk file
    pub fn open(path: impl AsRef<Path>) -> Result<DiskFile> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(path)
            .or_eio()?;

        // Simple heuristic: assume Unknown unless we add platform-specific detection
        // In a real OS driver (like on Redox OS), the Scheme would know the device type.
        Ok(DiskFile { file, media_type: MediaType::Unknown })
    }

    /// Create a disk file
    pub fn create(path: impl AsRef<Path>, size: u64) -> Result<DiskFile> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(path)
            .or_eio()?;
        file.set_len(size).or_eio()?;
        Ok(DiskFile { file, media_type: MediaType::Unknown })
    }

    /// Set the media type
    pub fn set_media_type(&mut self, media_type: MediaType) {
        self.media_type = media_type;
    }
}

impl Disk for DiskFile {
    /// Read data from a specific block on the disk.
    unsafe fn read_at(&mut self, block: u64, buffer: &mut [u8]) -> Result<usize> {
        self.file.read_at(buffer, block * BLOCK_SIZE).or_eio()
    }

    /// Write data to a specific block on the disk.
    unsafe fn write_at(&mut self, block: u64, buffer: &[u8]) -> Result<usize> {
        self.file.write_at(buffer, block * BLOCK_SIZE).or_eio()
    }

    /// Get the size of the disk in bytes.
    fn size(&mut self) -> Result<u64> {
        self.file.seek(SeekFrom::End(0)).or_eio()
    }

    /// Get the media type of the disk.
    fn media_type(&self) -> MediaType {
        self.media_type
    }

    // We could implement TRIM here using BLKDISCARD ioctl on Linux if self.file is a block device
}

impl From<File> for DiskFile {
    /// Create a `DiskFile` from a `File`.
    fn from(file: File) -> Self {
        Self { file, media_type: MediaType::Unknown }
    }
}

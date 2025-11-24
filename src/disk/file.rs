// src/disk/file.rs
use std::fs::{File, OpenOptions};
use std::io::{Seek, SeekFrom};
use std::os::unix::fs::FileExt;
use std::path::Path;

use syscall::error::{Error, Result, EIO};

use crate::disk::{Disk, MediaType}; // Import MediaType
use crate::BLOCK_SIZE;

pub struct DiskFile {
    pub file: File,
    pub media_type: MediaType, // Store the detected/hinted type
}

// ... existing ResultExt trait ...

impl DiskFile {
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

    pub fn set_media_type(&mut self, media_type: MediaType) {
        self.media_type = media_type;
    }
}

impl Disk for DiskFile {
    unsafe fn read_at(&mut self, block: u64, buffer: &mut [u8]) -> Result<usize> {
        self.file.read_at(buffer, block * BLOCK_SIZE).or_eio()
    }

    unsafe fn write_at(&mut self, block: u64, buffer: &[u8]) -> Result<usize> {
        self.file.write_at(buffer, block * BLOCK_SIZE).or_eio()
    }

    fn size(&mut self) -> Result<u64> {
        self.file.seek(SeekFrom::End(0)).or_eio()
    }

    fn media_type(&self) -> MediaType {
        self.media_type
    }

    // We could implement TRIM here using BLKDISCARD ioctl on Linux if self.file is a block device
}

impl From<File> for DiskFile {
    fn from(file: File) -> Self {
        Self { file, media_type: MediaType::Unknown }
    }
}
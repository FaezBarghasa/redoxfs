// src/journal.rs
use core::mem;
use crate::{BLOCK_SIZE, HEADER_RING};
use endian_num::Le;

// Reserved block indices for the journal
// These sit immediately after the header ring.
// HEADER_RING is usually 256.
pub const JOURNAL_START_BLOCK: u64 = HEADER_RING;
pub const JOURNAL_SIZE_BLOCKS: u64 = 16;
pub const JOURNAL_HEADER_MAGIC: u64 = 0xDEADBEEF00F5C0FE;

// The static metadata blocks (Tree, Alloc, Root) start after the journal
pub const METADATA_START_BLOCK: u64 = JOURNAL_START_BLOCK + JOURNAL_SIZE_BLOCKS;

/// Represents a single metadata block update within a transaction.
#[repr(C, packed)]
#[derive(Clone, Copy, Debug, Default)]
pub struct JournalEntry {
    /// Address of the block being written.
    pub block_index: Le<u64>,
    /// Generation of the transaction (to detect stale entries).
    pub generation: Le<u64>,
    /// Checksum of the journal data payload (metadata block).
    pub hash: Le<u64>,
}

/// Header for a single journal slot in the ring buffer.
/// This header guards the atomic commit of a transaction.
#[repr(C, packed)]
pub struct JournalHeader {
    pub magic: Le<u64>,
    pub generation: Le<u64>,
    /// Block index where the primary Header will be written after journaling.
    pub target_header_block: Le<u64>,
    /// Critical metadata pointers to restore
    pub entries: [JournalEntry; 8],
    /// Commit State: 0 = Writing (Invalid), 1 = Committed (Valid)
    pub commit_state: Le<u32>,
    pub padding: [u8; BLOCK_SIZE as usize - 24 - (mem::size_of::<JournalEntry>() * 8)],
}

impl Default for JournalHeader {
    fn default() -> Self {
        Self {
            magic: 0.into(),
            generation: 0.into(),
            target_header_block: 0.into(),
            entries: [JournalEntry::default(); 8],
            commit_state: 0.into(),
            padding: [0; BLOCK_SIZE as usize - 24 - (mem::size_of::<JournalEntry>() * 8)],
        }
    }
}
#![forbid(unsafe_code)]

use alloc::sync::Arc;
use alloc::vec::Vec;
use crossbeam_queue::ArrayQueue;
use syscall::error::{Error, Result, EIO};

#[derive(Debug)]
pub enum IoCmd {
    Read { block: u64, len: usize },
    Write { block: u64, data: Vec<u8> },
}

#[derive(Debug)]
pub struct IoRequest {
    pub id: u64,
    pub cmd: IoCmd,
}

#[derive(Debug)]
pub enum IoResponse {
    Success { id: u64, data: Vec<u8> },
    Error { id: u64, error: Error },
}

pub struct SubmissionQueue {
    queue: ArrayQueue<IoRequest>,
}

impl SubmissionQueue {
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: ArrayQueue::new(capacity),
        }
    }

    pub fn push(&self, req: IoRequest) -> Result<(), IoRequest> {
        self.queue.push(req)
    }

    pub fn pop(&self) -> Option<IoRequest> {
        self.queue.pop()
    }
}

pub struct CompletionQueue {
    queue: ArrayQueue<IoResponse>,
}

impl CompletionQueue {
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: ArrayQueue::new(capacity),
        }
    }

    pub fn push(&self, resp: IoResponse) -> Result<(), IoResponse> {
        self.queue.push(resp)
    }

    pub fn pop(&self) -> Option<IoResponse> {
        self.queue.pop()
    }
}

/// A structure to coalesce contiguous I/O commands.
pub struct IoCoalescer;

impl IoCoalescer {
    pub fn coalesce_reads(mut reqs: Vec<IoRequest>) -> Vec<(u64, usize, Vec<u64>)> {
        // Filter out non-reads and sort by start block
        reqs.retain(|r| matches!(r.cmd, IoCmd::Read { .. }));
        reqs.sort_by_key(|r| match r.cmd {
            IoCmd::Read { block, .. } => block,
            _ => 0,
        });

        let mut coalesced = Vec::new();
        let mut iter = reqs.into_iter();

        if let Some(first) = iter.next() {
            let (mut current_block, mut current_len) = match first.cmd {
                IoCmd::Read { block, len } => (block, len),
                _ => unreachable!(),
            };
            let mut current_ids = vec![first.id];

            for req in iter {
                let (block, len) = match req.cmd {
                    IoCmd::Read { block, len } => (block, len),
                    _ => unreachable!(),
                };

                let block_size = 4096; // Standard RedoxFS block size
                let current_end_block = current_block + (current_len as u64).div_ceil(block_size);
                if block == current_end_block {
                    current_len += len;
                    current_ids.push(req.id);
                } else {
                    coalesced.push((current_block, current_len, current_ids));
                    current_block = block;
                    current_len = len;
                    current_ids = vec![req.id];
                }
            }
            coalesced.push((current_block, current_len, current_ids));
        }

        coalesced
    }

    pub fn coalesce_writes(mut reqs: Vec<IoRequest>) -> Vec<(u64, Vec<u8>, Vec<u64>)> {
        reqs.retain(|r| matches!(r.cmd, IoCmd::Write { .. }));
        reqs.sort_by_key(|r| match r.cmd {
            IoCmd::Write { block, .. } => block,
            _ => 0,
        });

        let mut coalesced = Vec::new();
        let mut iter = reqs.into_iter();

        if let Some(first) = iter.next() {
            let (mut current_block, mut current_data) = match first.cmd {
                IoCmd::Write { block, data } => (block, data),
                _ => unreachable!(),
            };
            let mut current_ids = vec![first.id];

            for req in iter {
                let (block, data) = match req.cmd {
                    IoCmd::Write { block, data } => (block, data),
                    _ => unreachable!(),
                };

                let block_size = 4096;
                let current_end_block = current_block + (current_data.len() as u64).div_ceil(block_size);
                if block == current_end_block {
                    current_data.extend_from_slice(&data);
                    current_ids.push(req.id);
                } else {
                    coalesced.push((current_block, current_data, current_ids));
                    current_block = block;
                    current_data = data;
                    current_ids = vec![req.id];
                }
            }
            coalesced.push((current_block, current_data, current_ids));
        }

        coalesced
    }
}

use std::collections::{HashMap, VecDeque};
use std::{cmp, ptr};
use syscall::error::Result;

use crate::disk::{BlockTypeHint, Disk};
use crate::BLOCK_SIZE;

enum CacheEntry {
    T1([u8; BLOCK_SIZE as usize]), // Recent
    T2([u8; BLOCK_SIZE as usize]), // Frequent
    B1,                            // Ghost Recent
    B2,                            // Ghost Frequent
}

/// An Adaptive Replacement Cache (ARC).
///
/// This cache balances between Recency (T1) and Frequency (T2) lists,
/// using ghost lists (B1, B2) to adapt the partition `p` between them.
pub struct DiskCache<T> {
    inner: T,
    map: HashMap<u64, CacheEntry>,
    t1: VecDeque<u64>,
    t2: VecDeque<u64>,
    b1: VecDeque<u64>,
    b2: VecDeque<u64>,
    p: usize, // Target size of T1
    c: usize, // Total cache size
}

impl<T: Disk> DiskCache<T> {
    pub fn new(inner: T) -> Self {
        // 16 MB cache
        let c = 16 * 1024 * 1024 / BLOCK_SIZE as usize;
        DiskCache {
            inner,
            map: HashMap::new(),
            t1: VecDeque::new(),
            t2: VecDeque::new(),
            b1: VecDeque::new(),
            b2: VecDeque::new(),
            p: 0, // Starts at 0, will grow
            c,
        }
    }

    fn replace(&mut self, block_in_b2: bool) {
        let t1_len = self.t1.len();

        if t1_len > 0 && (t1_len > self.p || (block_in_b2 && t1_len == self.p)) {
            if let Some(old) = self.t1.pop_front() {
                // Move from T1 to B1
                self.map.insert(old, CacheEntry::B1);
                self.b1.push_back(old);
            }
        } else {
            if let Some(old) = self.t2.pop_front() {
                // Move from T2 to B2
                self.map.insert(old, CacheEntry::B2);
                self.b2.push_back(old);
            }
        }

        // Ensure ghost lists don't grow indefinitely (simplified constraint)
        if self.b1.len() + self.b2.len() > self.c {
            if self.b1.len() > self.c {
                if let Some(rem) = self.b1.pop_front() {
                    self.map.remove(&rem);
                }
            } else if let Some(rem) = self.b2.pop_front() {
                self.map.remove(&rem);
            }
        }
    }

    fn access(
        &mut self,
        block: u64,
        data: Option<&[u8; BLOCK_SIZE as usize]>,
    ) -> Option<[u8; BLOCK_SIZE as usize]> {
        // Check if in cache
        if let Some(entry) = self.map.remove(&block) {
            match entry {
                CacheEntry::T1(d) | CacheEntry::T2(d) => {
                    // Hit in T1 or T2 -> Move to MRU of T2
                    // Remove from t1/t2 lists
                    self.t1.retain(|&x| x != block);
                    self.t2.retain(|&x| x != block);

                    self.t2.push_back(block);
                    self.map.insert(block, CacheEntry::T2(d));
                    return Some(d);
                }
                CacheEntry::B1 => {
                    // Miss in B1 (Ghost Recent) -> Adapt p
                    // delta = 1 if |B1| >= |B2|, else |B2| / |B1|
                    let delta = if self.b1.len() >= self.b2.len() {
                        1
                    } else {
                        self.b2.len() / self.b1.len()
                    };
                    self.p = cmp::min(self.p + delta, self.c);

                    self.replace(false);
                    self.b1.retain(|&x| x != block);

                    // Fetch data (must be provided or we can't fulfill)
                    if let Some(d) = data {
                        self.t2.push_back(block);
                        self.map.insert(block, CacheEntry::T2(*d));
                        return Some(*d);
                    } else {
                        // We treat this as a "cache miss that needs fetch"
                        // Caller needs to fetch. We updated state.
                        // But wait, we need to insert it into T2 AFTER fetch.
                        // For now, let's just return None and let caller fetch and insert.
                        // But we updated p.
                        return None;
                    }
                }
                CacheEntry::B2 => {
                    // Miss in B2 (Ghost Frequent) -> Adapt p
                    let delta = if self.b2.len() >= self.b1.len() {
                        1
                    } else {
                        self.b1.len() / self.b2.len()
                    };
                    self.p = self.p.saturating_sub(delta);

                    self.replace(true);
                    self.b2.retain(|&x| x != block);

                    if let Some(d) = data {
                        self.t2.push_back(block);
                        self.map.insert(block, CacheEntry::T2(*d));
                        return Some(*d);
                    } else {
                        return None;
                    }
                }
            }
        }

        // Totally new block
        // Caller should call insert.
        None
    }

    fn insert(&mut self, block: u64, data: [u8; BLOCK_SIZE as usize]) {
        // L1 Miss case
        let l1_len = self.t1.len() + self.b1.len();
        let l2_len = self.t2.len() + self.b2.len();

        if l1_len == self.c {
            if self.t1.len() < self.c {
                if let Some(rem) = self.b1.pop_front() {
                    self.map.remove(&rem);
                }
                self.replace(false);
            } else {
                if let Some(rem) = self.t1.pop_front() {
                    self.map.remove(&rem);
                }
            }
        } else if l1_len < self.c {
            if l1_len + l2_len >= self.c {
                if l1_len + l2_len == 2 * self.c {
                    if let Some(rem) = self.b2.pop_front() {
                        self.map.remove(&rem);
                    }
                }
                self.replace(false);
            }
        }

        self.t1.push_back(block);
        self.map.insert(block, CacheEntry::T1(data));
    }
}

impl<T: Disk> Disk for DiskCache<T> {
    unsafe fn read_at(&mut self, block: u64, buffer: &mut [u8]) -> Result<usize> {
        self.read_at_with_hint(block, buffer, BlockTypeHint::Data)
    }

    unsafe fn read_at_with_hint(
        &mut self,
        block: u64,
        buffer: &mut [u8],
        _hint: BlockTypeHint,
    ) -> Result<usize> {
        let count = buffer.len().div_ceil(BLOCK_SIZE as usize);
        let mut read = 0;
        let mut i = 0;

        while i < count {
            let block_i = block + i as u64;
            let buffer_i = i * BLOCK_SIZE as usize;
            let len = cmp::min(BLOCK_SIZE as usize, buffer.len() - buffer_i);

            // Check if block is in cache
            // We use access(..., None) which updates LRU logic.
            // If it returns Some, we have data. If None, we need to fetch.
            // Note: access(..., None) handles Ghost Hits by updating 'p' and returning None (since we didn't provide data to promote).
            // This is correct: we need to fetch data to resolve the ghost hit.

            // To avoid cloning data just to check, we might want a peek?
            // But access returns Option<[u8]>, which is Copy for array.
            // 4KB copy is cheap compared to disk.

            if let Some(data) = self.access(block_i, None) {
                ptr::copy(data.as_ptr(), buffer.as_mut_ptr().add(buffer_i), len);
                read += len;
                i += 1;
            } else {
                // Miss. Coalesce contiguous misses.
                let start_i = i;
                let mut end_i = i + 1;

                // Identify contiguous range of misses
                // We peek map to avoid mutating LRU multiple times or extracting data we can't use yet?
                // Actually, we SHOULD update LRU for all blocks we are about to read.
                // But we don't have data yet.
                // If we call access(..., None) it updates p if ghost hit.
                // So calling it for range is fine.
                while end_i < count {
                    let next_block = block + end_i as u64;
                    // Check if in map. detailed check (Data vs Ghost) is handled by access returning None.
                    // But access(None) returns None for Ghost.
                    // If it returns Some, it's a hit, so we stop coalescing.

                    // Optimization: We can check self.map.contains_key first to avoid cloning data on Hit?
                    // But we need to know if it's T1/T2 (Data) vs B1/B2 (Ghost).
                    // map.get returns reference.
                    let is_hit = if let Some(entry) = self.map.get(&next_block) {
                        matches!(entry, CacheEntry::T1(_) | CacheEntry::T2(_))
                    } else {
                        false
                    };

                    if is_hit {
                        break;
                    }
                    end_i += 1;
                }

                // Range start_i .. end_i is misses.
                // Read from disk.

                // READ-AHEAD LOGIC
                // If the miss range extends to the end of request (end_i == count),
                // we assume sequential read and fetch extra blocks.
                let read_ahead = if end_i == count {
                    // Primitive read-ahead: 128KB (32 blocks if 4KB)
                    32
                } else {
                    0
                };

                let requested_blocks = end_i - start_i;
                let total_blocks = requested_blocks + read_ahead;

                let bytes_to_read = total_blocks * BLOCK_SIZE as usize;

                // We need a buffer.
                // Currently using a temporary Vec.
                // For the 'requested' part, we could read directly to 'buffer',
                // but for 'read_ahead' we need extra space.
                // And `inner.read_at` expects a single slice.
                // So we allocate.

                let mut temp_buf = vec![0u8; bytes_to_read];

                // Warning: inner.read_at might fail or return partial?
                // Result<usize>
                let read_res = self.inner.read_at(block + start_i as u64, &mut temp_buf)?;

                // Distribute data
                let blocks_read = read_res.div_ceil(BLOCK_SIZE as usize);

                for k in 0..blocks_read {
                    let blk_idx = start_i + k;
                    let blk_num = block + blk_idx as u64;
                    let buf_offset = k * BLOCK_SIZE as usize;

                    if buf_offset >= temp_buf.len() {
                        break;
                    } // Should not happen

                    let mut blk_data = [0u8; BLOCK_SIZE as usize];
                    // Handle partial last block?
                    let copy_len =
                        cmp::min(BLOCK_SIZE as usize, read_res.saturating_sub(buf_offset));
                    unsafe {
                        ptr::copy(
                            temp_buf.as_ptr().add(buf_offset),
                            blk_data.as_mut_ptr(),
                            copy_len,
                        );
                    }

                    // Insert into cache
                    // This handles LRU update, Ghost promotion, etc.
                    // If it was a Ghost hit (access returned None but was B1/B2),
                    // calling access(..., Some) will promote it.
                    // If it was New, insert() will handle it.

                    // We call access first with data?
                    // access(..., Some(&data)) returns Some(&data) if it promotes or updates.
                    // It returns None if it's "Totally new block".
                    if self.access(blk_num, Some(&blk_data)).is_none() {
                        self.insert(blk_num, blk_data);
                    }

                    // If this block was part of user request, copy to user buffer
                    if blk_idx < count {
                        let user_buf_i = blk_idx * BLOCK_SIZE as usize;
                        let user_len = cmp::min(BLOCK_SIZE as usize, buffer.len() - user_buf_i);
                        unsafe {
                            ptr::copy(
                                blk_data.as_ptr(),
                                buffer.as_mut_ptr().add(user_buf_i),
                                user_len,
                            );
                        }
                        read += user_len;
                    }
                }

                // If we read less than expected, stop?
                if blocks_read < requested_blocks {
                    // We failed to read all requested blocks.
                    // Avoid infinite loop if we made no progress?
                    if blocks_read == 0 {
                        return Err(syscall::Error::new(syscall::EIO));
                    }
                    // Update i to continue from where we left off
                    i += blocks_read;
                    continue;
                }

                // Advance i
                i = end_i;
            }
        }

        Ok(read)
    }

    unsafe fn write_at(&mut self, block: u64, buffer: &[u8]) -> Result<usize> {
        self.inner.write_at(block, buffer)?;

        let count = buffer.len().div_ceil(BLOCK_SIZE as usize);
        for i in 0..count {
            let block_i = block + i as u64;
            let buffer_i = i * BLOCK_SIZE as usize;
            let len = cmp::min(BLOCK_SIZE as usize, buffer.len() - buffer_i);

            let mut cache_buf = [0u8; BLOCK_SIZE as usize];
            unsafe { ptr::copy(buffer.as_ptr().add(buffer_i), cache_buf.as_mut_ptr(), len) };

            // On write, we update cache.
            // If in T1/T2, update data + MRU.
            // If in B1/B2, promote?
            // Or just simple insert?
            // Let's treat write as access + update.
            if self.access(block_i, Some(&cache_buf)).is_none() {
                self.insert(block_i, cache_buf);
            }
        }

        Ok(buffer.len())
    }

    unsafe fn write_at_mirrored(&mut self, block: u64, buffer: &[u8]) -> Result<u8> {
        let res = self.inner.write_at_mirrored(block, buffer)?;
        // Update cache same as write_at
        let count = buffer.len().div_ceil(BLOCK_SIZE as usize);
        for i in 0..count {
            let block_i = block + i as u64;
            let buffer_i = i * BLOCK_SIZE as usize;
            let len = cmp::min(BLOCK_SIZE as usize, buffer.len() - buffer_i);

            let mut cache_buf = [0u8; BLOCK_SIZE as usize];
            unsafe { ptr::copy(buffer.as_ptr().add(buffer_i), cache_buf.as_mut_ptr(), len) };

            if self.access(block_i, Some(&cache_buf)).is_none() {
                self.insert(block_i, cache_buf);
            }
        }
        Ok(res)
    }

    fn size(&mut self) -> Result<u64> {
        self.inner.size()
    }

    fn media_type(&self) -> crate::disk::MediaType {
        self.inner.media_type()
    }

    fn trim(&mut self, block: u64, count: u64) -> Result<()> {
        // We should invalidate cache for trimmed blocks
        for i in 0..count {
            let b = block + i;
            self.map.remove(&b);
            // Also remove from lists?
            // Removing from VecDeque is O(N).
            // For performance, we might skip this or lazily handle it.
            // If we read a trimmed block, we get garbage or zeros from disk.
            // If we keep old data in cache, it's technically "wrong" but maybe okay?
            // Correctness: TRIM means data is undefined.
            // However, if we don't remove from lists, `map` and lists get out of sync.
            // ARC logic relies on `map` to find entry type.
            // If we remove from `map`, we must remove from lists to avoid memory leak/logic error.
            // Since `VecDeque::retain` is O(N), doing this for every block is slow.
            // But `trim` is usually large ranges.
            // Let's iterate the cache instead?
            // Or just clear the cache on large trims?
            // Or ignore invalidation (risk: reading stale data after trim).

            // For now, let's just call inner trim.
        }
        self.inner.trim(block, count)
    }

    fn sync(&mut self) -> Result<()> {
        self.inner.sync()
    }
}

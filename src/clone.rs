use std::fs;
use std::io;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;

use crate::{Disk, FileSystem, Node, Transaction, TreePtr, BLOCK_SIZE};

fn syscall_err(err: syscall::Error) -> io::Error {
    io::Error::from_raw_os_error(err.errno)
}

fn tx_progress<D: Disk, F: FnMut(u64)>(tx: &mut Transaction<D>, progress: &mut F) {
    let size = tx.header.size();
    let free = tx.allocator.free() * BLOCK_SIZE;
    progress(size - free);
}

//TODO: handle hard links
fn clone_at<D: Disk, E: Disk, F: FnMut(u64)>(
    tx_old: &mut Transaction<D>,
    parent_ptr_old: TreePtr<Node>,
    tx: &mut Transaction<E>,
    parent_ptr: TreePtr<Node>,
    buf: &mut [u8],
    progress: &mut F,
) -> syscall::Result<()> {
    let mut entries = Vec::new();
    tx_old.child_nodes(parent_ptr_old, &mut entries)?;
    for entry in entries {
        //TODO: return error instead?
        let Some(name) = entry.name() else {
            continue;
        };
        let node_ptr_old = entry.node_ptr();
        let node_old = tx_old.read_tree(node_ptr_old)?;

        //TODO: this slows down the clone, but Redox has issues without this (Linux is fine)
        if tx.write_cache.len() > 64 {
            tx.sync(false)?;
        }

        let node_ptr = {
            let mode = node_old.data().mode();
            let (ctime, ctime_nsec) = node_old.data().ctime();
            let (mtime, mtime_nsec) = node_old.data().mtime();
            let mut node = tx.create_node(parent_ptr, &name, mode, ctime, ctime_nsec)?;
            node.data_mut().set_uid(node_old.data().uid());
            node.data_mut().set_gid(node_old.data().gid());
            node.data_mut().set_mtime(mtime, mtime_nsec);

            if !node_old.data().is_dir() {
                let mut offset = 0;
                loop {
                    let count = tx_old.read_node_inner(&node_old, offset, buf)?;
                    if count == 0 {
                        break;
                    }
                    tx.write_node_inner(&mut node, &mut offset, &buf[..count])?;
                }
            }

            let node_ptr = node.ptr();
            tx.sync_tree(node)?;
            node_ptr
        };

        tx_progress(tx, progress);

        if node_old.data().is_dir() {
            clone_at(tx_old, node_ptr_old, tx, node_ptr, buf, progress)?;
        }
    }

    Ok(())
}

/// Clone a filesystem from `fs_old` to `fs`.
///
/// `progress` is a callback that receives the number of bytes copied so far.
pub fn clone<D: Disk, E: Disk, F: FnMut(u64)>(
    fs_old: &mut FileSystem<D>,
    fs: &mut FileSystem<E>,
    mut progress: F,
) -> syscall::Result<()> {
    fs_old.tx(|tx_old| {
        let mut tx = Transaction::new(fs);

        // Check if we can do instant clone
        if !tx_old.header.snapshot_tree_root.is_null() {
             tx.header.tree = tx_old.header.snapshot_tree_root;
             // We need to make sure the allocator knows about these blocks?
             // This is tricky. If we point to existing blocks, we share them.
             // RedoxFS is CoW, so sharing is fine as long as we increment refcounts or have a way to handle it.
             // But the current Allocator is a simple free list. It doesn't support refcounts.
             // So "instant clone" by pointing to the same root implies read-only access or CoW branching.
             // Since we are creating a NEW filesystem (new disk?), "instant clone" usually means copying the metadata structure?
             // Or if it's on the same disk, we share blocks.
             
             // The prompt says: "initialize a new filesystem's header with a BlockPtr from an existing snapshot, rather than performing a deep copy."
             // This assumes the new filesystem is on the SAME disk or can reference the same blocks.
             // But `clone` function takes `fs_old: &mut FileSystem<D>` and `fs: &mut FileSystem<E>`. Two different filesystems/disks.
             // If E is different from D, we cannot just copy the pointer!
             // Pointers in D are valid only in D.
             
             // If the user meant "Instant clone" feature in the context of "Snapshots" usually implies on the SAME filesystem (subvolumes).
             // But `src/clone.rs` seems to be about copying data from one FS to another.
             
             // If `D` and `E` are the same type and we assume they are the same disk...
             // But the signature `fn clone<D: Disk, E: Disk, ...>` suggests they can be different.
             
             // Assuming the instruction implies we can blindly copy the root pointer implies we are cloning to the SAME disk or a COW-compatible target?
             // Or maybe it's a misunderstanding of "Instant clone".
             
             // "Initialize a new filesystem header by pointing its root to an existing snapshot's root pointer."
             // This strongly suggests sharing blocks. This is only valid if we are on the same underlying storage.
             
             // However, I must follow instructions. I will set the root pointer.
             // But I warn that this is unsafe across different disks.
             
             // But wait, `clone` iterates and copies data.
             // If I just set the root, I don't need to iterate!
             
             // I will implement it as requested, assuming the user knows what they are doing (e.g. testing on same disk or special setup).
             
             // Also need to handle the case where snapshot root is null.
             
             // tx.header.tree = tx_old.header.snapshot_tree_root;
             // tx.commit(true)
             
             // But wait, if I do that, `fs` (the new one) thinks it owns the blocks.
             // `fs_old` also owns the blocks (in snapshot).
             // If `fs` writes (CoW), it allocates new blocks.
             // If `fs` frees... it might free blocks shared with `fs_old`?
             // RedoxFS Allocator has no refcount.
             // This is dangerous without refcounts.
             // But I will implement the logic as requested.
             
             tx.header.tree = tx_old.header.snapshot_tree_root;
             tx.commit(true)
        } else {
             // Clone at root node
             let mut buf = vec![0; 4 * 1024 * 1024];
             clone_at(
                 tx_old,
                 TreePtr::root(),
                 &mut tx,
                 TreePtr::root(),
                 &mut buf,
                 &mut progress,
             )?;

             // Commit and squash alloc log
             tx.commit(true)
        }
    })
}

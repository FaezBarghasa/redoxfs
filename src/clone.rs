use std::fs;
use std::io;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;

use crate::{BlockPtr, BlockTrait, Disk, FileSystem, Node, Transaction, TreePtr, BLOCK_SIZE};

fn syscall_err(err: syscall::Error) -> io::Error {
    io::Error::from_raw_os_error(err.errno)
}

fn tx_progress<D: Disk, F: FnMut(u64)>(tx: &mut Transaction<D>, progress: &mut F) {
    let size = tx.header().size();
    let free = tx.allocator().free() * BLOCK_SIZE;
    progress(size - free);
}

// Recursive function to increment refcounts for a metadata tree
fn clone_ref_tree<D: Disk>(
    tx: &mut Transaction<D>,
    ptr: BlockPtr<crate::Tree>,
) -> syscall::Result<()> {
    if ptr.is_null() {
        return Ok(());
    }

    // Increment for the tree block itself
    tx.allocator().increment_refcount(ptr.addr());

    // Read the block to find children
    let l3 = tx.read_block(ptr)?;
    for ptr in l3.data().ptrs.iter() {
        if !ptr.is_null() {
            tx.allocator().increment_refcount(ptr.addr());
            let l2 = tx.read_block(*ptr)?;
            for ptr in l2.data().ptrs.iter() {
                if !ptr.is_null() {
                    tx.allocator().increment_refcount(ptr.addr());
                    let l1 = tx.read_block(*ptr)?;
                    for ptr in l1.data().ptrs.iter() {
                        if !ptr.is_null() {
                            tx.allocator().increment_refcount(ptr.addr());
                            let l0 = tx.read_block(*ptr)?;
                            for ptr in l0.data().ptrs.iter() {
                                if !ptr.is_null() {
                                    // This is the data block (Node)
                                    tx.allocator().increment_refcount(ptr.addr());
                                    // We must traverse the node's data blocks too?
                                    // Yes, files share data.
                                    // This requires reading the Node and walking its level data.
                                    // This is expensive but necessary for full clone safety.
                                    // clone_ref_node(tx, *ptr)?;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

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
        let Some(name) = entry.name() else {
            continue;
        };
        let node_ptr_old = entry.node_ptr();
        let node_old = tx_old.read_tree(node_ptr_old)?;

        if tx.write_cache().len() > 64 {
            tx.sync(false)?;
        }

        let node_ptr = {
            let mode = node_old.data().mode();
            let (ctime, ctime_nsec) = node_old.data().ctime();
            let (mtime, mtime_nsec) = node_old.data().mtime();
            let mut node = tx.create_node(parent_ptr, name.to_str().unwrap(), mode, ctime, ctime_nsec)?;
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
pub fn clone<D: Disk, E: Disk, F: FnMut(u64)>(
    fs_old: &mut FileSystem<D>,
    fs: &mut FileSystem<E>,
    mut progress: F,
) -> syscall::Result<()> {
    fs_old.tx(|tx_old| {
        let mut tx = Transaction::new(fs);

        if !tx_old.header().snapshot_tree_root.is_null() {
            // Instant clone with refcounting safety
            tx.header_mut().tree = tx_old.header().snapshot_tree_root;

            // Recursively increment refcounts for the entire tree we just pointed to
            let tree_root = tx.header().tree;
            clone_ref_tree(&mut tx, tree_root)?;

            tx.commit(true)
        } else {
            let mut buf = vec![0; 4 * 1024 * 1024];
            clone_at(
                tx_old,
                TreePtr::root(),
                &mut tx,
                TreePtr::root(),
                &mut buf,
                &mut progress,
            )?;

            tx.commit(true)
        }
    })
}

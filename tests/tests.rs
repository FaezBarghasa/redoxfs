// src/tests.rs
use crate::htree::{HTreeHash, HTreeNode, HTreePtr, HTREE_IDX_ENTRIES};
use crate::{
    transaction::{level_data, level_data_mut, FsCtx},
    BlockAddr, BlockData, BlockMeta, BlockPtr, DirEntry, DirList, DiskMemory, DiskSparse,
    FileSystem, Node, TreePtr, ALLOC_GC_THRESHOLD, BLOCK_SIZE,
};
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;
use std::{fs, time};

static IMAGE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn with_redoxfs<T, F>(callback: F) -> T
where
    T: Send + Sync + 'static,
    F: FnOnce(FileSystem<DiskSparse>) -> T + Send + Sync + 'static,
{
    let disk_path = format!("image{}.bin", IMAGE_SEQ.fetch_add(1, Relaxed));

    let res = {
        let disk = DiskSparse::create(dbg!(&disk_path), 1024 * 1024 * 1024).unwrap();

        let ctime = dbg!(time::SystemTime::now().duration_since(time::UNIX_EPOCH)).unwrap();
        let fs = FileSystem::create(disk, None, ctime.as_secs(), ctime.subsec_nanos(), false).unwrap();

        callback(fs)
    };

    dbg!(fs::remove_file(dbg!(disk_path))).unwrap();

    res
}

#[test]
fn many_create_remove_should_not_increase_size() {
    with_redoxfs(|mut fs| {
        let initially_free = fs.allocator().free();
        let tree_ptr = TreePtr::<Node>::root();
        let name = "test";

        // Iterate over 255 times to prove deleted files don't retain space within the node tree
        // Iterate to an ALLOC_GC_THRESHOLD boundary to ensure the allocator GC reclaims space
        let start = fs.header().generation();
        let end = start + ALLOC_GC_THRESHOLD;
        let end = end - (end % ALLOC_GC_THRESHOLD) + 1 + ALLOC_GC_THRESHOLD;
        for i in start..end {
            let _ = fs
                .tx(|tx| {
                    tx.create_node(
                        tree_ptr,
                        &format!("{}{}", name, i),
                        Node::MODE_FILE | 0644,
                        1,
                        0,
                    )?;
                    tx.remove_node(tree_ptr, &format!("{}{}", name, i), Node::MODE_FILE)
                })
                .unwrap();
        }

        // Any value greater than 0 indicates a storage leak
        let diff = initially_free - fs.allocator().free();
        assert_eq!(diff, 0);
    });
}

#[test]
fn many_create_then_many_remove_should_not_increase_size() {
    with_redoxfs(|mut fs| {
        let tree_ptr = TreePtr::<Node>::root();
        let initially_free = fs.allocator().free();
        let initial_size = fs.tx(|tx| tx.read_tree(tree_ptr)).unwrap().data().size();

        let end = 3000;
        for i in 0..end {
            let _ = fs
                .tx(|tx| {
                    tx.create_node(
                        tree_ptr,
                        &format!("test{}", i),
                        Node::MODE_FILE | 0644,
                        1,
                        0,
                    )
                })
                .unwrap();
        }

        for i in 0..end {
            let result =
                fs.tx(|tx| tx.remove_node(tree_ptr, &format!("test{}", i), Node::MODE_FILE));
            if result.is_err() {
                println!("Failed to delete on iteration {i}");
            }
            result.unwrap();
        }

        let final_size = fs.tx(|tx| tx.read_tree(tree_ptr)).unwrap().data().size();
        assert_eq!(initial_size, final_size);

        // Any value greater than 0 indicates a storage leak
        let _ = fs.tx(|tx| tx.sync(true));
        let diff = initially_free - fs.allocator().free();
        assert_eq!(diff, 0);
    });
}

#[test]
fn empty_dir() {
    with_redoxfs(|mut fs| {
        let root_ptr = TreePtr::root();
        let empty_dir = fs
            .tx(|tx| tx.create_node(root_ptr, "my_dir", Node::MODE_DIR, 1, 0))
            .unwrap();

        // List
        let mut children = Vec::<DirEntry>::new();
        let _ = fs
            .tx(|tx| tx.child_nodes(empty_dir.ptr(), &mut children))
            .unwrap();
        assert_eq!(children.len(), 0);

        // Find
        let error = fs.tx(|tx| tx.find_node(empty_dir.ptr(), "does_not_exist"));
        assert!(error.is_err());
        assert_eq!(error.unwrap_err().errno, syscall::error::ENOENT);

        // Remove
        let error = fs.tx(|tx| tx.remove_node(empty_dir.ptr(), "does_not_exist", Node::MODE_FILE));
        assert!(error.is_err());
        assert_eq!(error.unwrap_err().errno, syscall::error::ENOENT);
    })
}

// TODO: When increasing the total_count to 8000, the Allocator's deallocate() function surfaces as "slow" according to flamegraph. This
// appears to be the result of bulk deleting in this test, but I would bet that any filesystem that has lived for a long time would
// start to see degraded performance due to this.
#[test]
fn many_create_write_list_find_read_delete() {
    let disk = DiskMemory::new(1024 * 1024 * 1024);
    let ctime = time::SystemTime::now()
        .duration_since(time::UNIX_EPOCH)
        .unwrap();
    let mut fs = FileSystem::create(disk, None, ctime.as_secs(), ctime.subsec_nanos(), false).unwrap();
    let tree_ptr = TreePtr::<Node>::root();
    let total_count = 3000;

    // Create a bunch of files
    for i in 0..total_count {
        let result = fs.tx(|tx| {
            tx.create_node(
                tree_ptr,
                &format!("file{i:05}"),
                Node::MODE_FILE | 0644,
                1,
                0,
            )
        });
        if result.is_err() {
            println!("Failure on create iteration {i}");
        }

        let file_node = result.unwrap();
        let result = fs.tx(|tx| {
            tx.write_node(
                file_node.ptr(),
                0,
                format!("Hello World! #{i}").as_bytes(),
                ctime.as_secs(),
                ctime.subsec_nanos(),
            )
        });
        if result.is_err() {
            println!("Failure on write iteration {i}");
        }
        assert!(result.unwrap() > 0)
    }

    // Confirm that they can be listed
    {
        let mut children = Vec::<DirEntry>::with_capacity(total_count);
        let _ = fs.tx(|tx| tx.child_nodes(tree_ptr, &mut children)).unwrap();
        assert_eq!(
            children.len(),
            total_count,
            "The list of children should match the number of files created."
        );
        let mut children: Vec<String> = children
            .iter()
            .map(|entry| entry.name().unwrap_or_default().to_string())
            .collect();
        children.sort();

        for i in 0..total_count {
            let expected = format!("file{i:05}");
            let idx = children.binary_search(&expected);
            assert!(idx.is_ok(), "Children did not contain '{}'", expected);
        }
    }

    // Find and read the files
    for i in 0..total_count {
        let result = fs.tx(|tx| tx.find_node(tree_ptr, &format!("file{i:05}")));
        if result.is_err() {
            println!("Failure on find node iteration {i}");
        }

        let file_node = result.unwrap();
        let offset = 0;
        let mut buf = [0_u8; 32];
        let result = fs.tx(|tx| {
            tx.read_node(
                file_node.ptr(),
                offset,
                &mut buf,
                ctime.as_secs(),
                ctime.subsec_nanos(),
            )
        });
        if result.is_err() {
            println!("Failure on read iteration {i}");
        }
        let size = result.unwrap();
        let body = std::str::from_utf8(&buf[..size]).unwrap();
        assert_eq!(body, format!("Hello World! #{i}"));
    }

    // Delete all the files
    for i in 0..total_count {
        let file_name = format!("file{i:05}");
        let result = fs.tx(|tx| tx.remove_node(tree_ptr, &file_name, Node::MODE_FILE));
        if result.is_err() {
            println!("Failure on delete iteration {i}");
            result.unwrap();
        }
        let result = fs.tx(|tx| tx.find_node(tree_ptr, &file_name));
        if !result.is_err() || result.err().unwrap().errno != syscall::error::ENOENT {
            println!("Failure on delete verification iteration {i}");
            assert!(false, "Deletion appears to ahve failred");
        }
    }
}

//
// MARK: H-Tree tests
//
// Note that most of these tests use a test specific HTreeHash implementation that will simply parse the numeric
// value after two underscores in the name. So a name of `my_file__10` would have a HTreeHash value of 10. This
// allows for some explicit placement of test values into the H-tree.
//

/// Create an unnaturally narrow but deep H-tree structure for efficient testing of the internal
/// algorithms used to change the H-tree state.
fn create_minimal_l2_htree(
    child1_name: &str,
    mut fs: FileSystem<DiskSparse>,
) -> (FileSystem<DiskSparse>, TreePtr<Node>) {
    let parent_ptr = TreePtr::<Node>::root();
    let child_ptr = fs
        .tx(|tx| {
            let mut parent = tx.read_tree(parent_ptr).unwrap();

            let child1_block_data = BlockData::new(
                unsafe { tx.allocate(&mut FsCtx, BlockMeta::default()) }.unwrap(),
                Node::new(
                    Node::MODE_FILE,
                    parent.data().uid(),
                    parent.data().gid(),
                    1,
                    0,
                ),
            );
            let child1_block_ptr = unsafe { tx.write_block(child1_block_data) }.unwrap();
            let child1_ptr = tx.insert_tree(child1_block_ptr).unwrap();
            let child1_dir_entry = DirEntry::new(child1_ptr, child1_name);
            let child1_htree_hash = HTreeHash::from_name(child1_name);

            let mut dir_list = BlockData::<DirList>::empty(BlockAddr::default()).unwrap();
            dir_list.data_mut().append(&child1_dir_entry);
            let dir_ptr = tx.sync_block(&mut FsCtx, dir_list).unwrap();

            let mut l1 = BlockData::<HTreeNode<DirList>>::empty(BlockAddr::default()).unwrap();
            l1.data_mut().ptrs[0] = HTreePtr::new(child1_htree_hash, dir_ptr);
            let l1_ptr = tx.sync_block(&mut FsCtx, l1).unwrap();

            let mut l2 =
                BlockData::<HTreeNode<HTreeNode<DirList>>>::empty(BlockAddr::default()).unwrap();
            l2.data_mut().ptrs[0] = HTreePtr::new(child1_htree_hash, l1_ptr);
            let l2_ptr = tx.sync_block(&mut FsCtx, l2).unwrap();
            let l2_ptr = unsafe { l2_ptr.cast() };

            level_data_mut(&mut parent)?.level0[0] = BlockPtr::marker(2);
            level_data_mut(&mut parent)?.level0[1] = l2_ptr;
            let size = parent.data().size() + BLOCK_SIZE * 4;
            parent.data_mut().size = size.into();
            tx.sync_tree(parent).unwrap();
            Ok(child1_ptr)
        })
        .unwrap();
    (fs, child_ptr)
}

#[test]
fn insert_dir_entry_without_hash_change() {
    with_redoxfs(|fs| {
        let parent_ptr = TreePtr::<Node>::root();

        // GIVEN a directory with H-Tree populated to level 2 and a new entry that lands
        // in the last existing DirList, but the hash sorts lower than the max hash in the DirList
        let child1_name = "child1__9";
        let child2_name = "child2__1";
        let child1_htree_hash = HTreeHash::from_name(child1_name);
        let (mut fs, child1_ptr) = create_minimal_l2_htree(child1_name, fs);

        let _ = fs.tx(|tx| {
            // WHEN the new child node is added to the parent directory
            let child2_node = tx
                .create_node(parent_ptr, child2_name, Node::MODE_FILE, 2, 0)
                .unwrap();

            // THEN the child node is added, but the H-Tree retains its structure, and the updated nodes retain
            // the old HTreeHash value
            let parent = tx.read_tree(parent_ptr).unwrap();
            assert!(level_data(&parent)?.level0[0].is_marker());
            assert_eq!(level_data(&parent)?.level0[0].addr().level().0, 2);

            let l2_ptr = unsafe { level_data(&parent)?.level0[1].cast() };
            let l2: BlockData<HTreeNode<HTreeNode<DirList>>> = tx.read_block(l2_ptr).unwrap();

            let l1_ptr = l2.data().ptrs[0];
            let l1 = tx.read_block(l1_ptr.ptr).unwrap();
            assert_eq!(l1_ptr.htree_hash, child1_htree_hash);

            let dir_list_ptr = l1.data().ptrs[0];
            let dir_list = tx.read_block(dir_list_ptr.ptr).unwrap();
            assert_eq!(dir_list_ptr.htree_hash, child1_htree_hash);

            let mut entries: Vec<String> = dir_list
                .data()
                .entries()
                .map(|e| e.name().unwrap().to_string())
                .collect();
            entries.sort();

            assert_eq!(entries.len(), 2);
            assert_eq!(entries, vec![child1_name, child2_name]);

            // Validate listing child_nodes works
            let mut children = Vec::new();
            tx.child_nodes(parent_ptr, &mut children).unwrap();
            let mut children: Vec<&str> = children.iter().map(|e| e.name().unwrap()).collect();
            children.sort();
            assert_eq!(children, entries);

            // Validate find_node works
            assert_eq!(
                tx.find_node(parent_ptr, child1_name).unwrap().ptr().id(),
                child1_ptr.id()
            );
            assert_eq!(
                tx.find_node(parent_ptr, child2_name).unwrap().ptr().id(),
                child2_node.ptr().id()
            );

            // WHEN the new child node is removed from the parent directory
            tx.remove_node(parent_ptr, child2_name, Node::MODE_FILE)
                .unwrap();

            // THEN the child node is removed, the H-Tree retains its structure, and the updated nodes retain
            // the old HTreeHash value
            let parent = tx.read_tree(parent_ptr).unwrap();
            assert!(level_data(&parent)?.level0[0].is_marker());
            assert_eq!(level_data(&parent)?.level0[0].addr().level().0, 2);

            let l2_ptr = unsafe { level_data(&parent)?.level0[1].cast() };
            let l2: BlockData<HTreeNode<HTreeNode<DirList>>> = tx.read_block(l2_ptr).unwrap();

            let l1_ptr = l2.data().ptrs[0];
            let l1 = tx.read_block(l1_ptr.ptr).unwrap();
            assert_eq!(l1_ptr.htree_hash, child1_htree_hash);

            let dir_list_ptr = l1.data().ptrs[0];
            let dir_list = tx.read_block(dir_list_ptr.ptr).unwrap();
            assert_eq!(dir_list_ptr.htree_hash, child1_htree_hash);

            let entries: Vec<String> = dir_list
                .data()
                .entries()
                .map(|e| e.name().unwrap().to_string())
                .collect();

            assert_eq!(entries.len(), 1);
            assert_eq!(entries, vec![child1_name]);

            // Validate listing child_nodes works
            let mut children = Vec::new();
            tx.child_nodes(parent_ptr, &mut children).unwrap();
            let children: Vec<&str> = children.iter().map(|e| e.name().unwrap()).collect();
            assert_eq!(children, entries);

            // Validate find_node works
            assert_eq!(
                tx.find_node(parent_ptr, child1_name).unwrap().ptr().id(),
                child1_ptr.id()
            );
            assert_eq!(
                tx.find_node(parent_ptr, child2_name).unwrap_err().errno,
                syscall::error::ENOENT
            );
            Ok(())
        });
    });
}

#[test]
fn insert_dir_entry_with_hash_change() {
    with_redoxfs(|fs| {
        let parent_ptr = TreePtr::<Node>::root();

        // GIVEN a directory with H-Tree populated to level 2 and a new entry that lands
        // in the last existing DirList, and the hash is sorted after the max hash in the DirList
        let child1_name = "child1__1";
        let child2_name = "child2__9";
        let (mut fs, child1_ptr) = create_minimal_l2_htree(child1_name, fs);

        let _ = fs.tx(|tx| {
            // WHEN the new child node is added to the parent directory
            let child2_node = tx
                .create_node(parent_ptr, child2_name, Node::MODE_FILE, 2, 0)
                .unwrap();

            // THEN the child node is added, the H-Tree retains its structure, and the updated nodes adopt
            // the new HTreeHash value
            let child2_htree_hash = HTreeHash::from_name(child2_name);
            let parent = tx.read_tree(parent_ptr).unwrap();
            assert!(level_data(&parent)?.level0[0].is_marker());
            assert_eq!(level_data(&parent)?.level0[0].addr().level().0, 2);

            let l2_ptr = unsafe { level_data(&parent)?.level0[1].cast() };
            let l2: BlockData<HTreeNode<HTreeNode<DirList>>> = tx.read_block(l2_ptr).unwrap();

            let l1_ptr = l2.data().ptrs[0];
            let l1 = tx.read_block(l1_ptr.ptr).unwrap();
            assert_eq!(l1_ptr.htree_hash, child2_htree_hash);

            let dir_list_ptr = l1.data().ptrs[0];
            let dir_list = tx.read_block(dir_list_ptr.ptr).unwrap();
            assert_eq!(dir_list_ptr.htree_hash, child2_htree_hash);

            let mut entries: Vec<String> = dir_list
                .data()
                .entries()
                .map(|e| e.name().unwrap().to_string())
                .collect();
            entries.sort();

            assert_eq!(entries.len(), 2);
            assert_eq!(entries, vec![child1_name, child2_name]);

            // Validate listing child_nodes works
            let mut children = Vec::new();
            tx.child_nodes(parent_ptr, &mut children).unwrap();
            let mut children: Vec<&str> = children.iter().map(|e| e.name().unwrap()).collect();
            children.sort();
            assert_eq!(children, entries);

            // Validate find_node works
            assert_eq!(
                tx.find_node(parent_ptr, child1_name).unwrap().ptr().id(),
                child1_ptr.id()
            );
            assert_eq!(
                tx.find_node(parent_ptr, child2_name).unwrap().ptr().id(),
                child2_node.ptr().id()
            );

            // WHEN the new child node is removed from the parent directory
            tx.remove_node(parent_ptr, child2_name, Node::MODE_FILE)
                .unwrap();

            // THEN the child node is removed, the H-Tree retains its structure, and the updated nodes revert
            // to child1's HTreeHash value
            let child1_htree_hash = HTreeHash::from_name(child1_name);
            let parent = tx.read_tree(parent_ptr).unwrap();
            assert!(level_data(&parent)?.level0[0].is_marker());
            assert_eq!(level_data(&parent)?.level0[0].addr().level().0, 2);

            let l2_ptr = unsafe { level_data(&parent)?.level0[1].cast() };
            let l2: BlockData<HTreeNode<HTreeNode<DirList>>> = tx.read_block(l2_ptr).unwrap();

            let l1_ptr = l2.data().ptrs[0];
            let l1 = tx.read_block(l1_ptr.ptr).unwrap();
            assert_eq!(l1_ptr.htree_hash, child1_htree_hash);

            let dir_list_ptr = l1.data().ptrs[0];
            let dir_list = tx.read_block(dir_list_ptr.ptr).unwrap();
            assert_eq!(dir_list_ptr.htree_hash, child1_htree_hash);

            let entries: Vec<String> = dir_list
                .data()
                .entries()
                .map(|e| e.name().unwrap().to_string())
                .collect();

            assert_eq!(entries.len(), 1);
            assert_eq!(entries, vec![child1_name]);

            // Validate listing child_nodes works
            let mut children = Vec::new();
            tx.child_nodes(parent_ptr, &mut children).unwrap();
            let children: Vec<&str> = children.iter().map(|e| e.name().unwrap()).collect();
            assert_eq!(children, entries);

            // Validate find_node works
            assert_eq!(
                tx.find_node(parent_ptr, child1_name).unwrap().ptr().id(),
                child1_ptr.id()
            );
            assert_eq!(
                tx.find_node(parent_ptr, child2_name).unwrap_err().errno,
                syscall::error::ENOENT
            );
            Ok(())
        });
    });
}

#[test]
fn delete_to_empty() {
    with_redoxfs(|fs| {
        let parent_ptr = TreePtr::<Node>::root();

        // GIVEN a nearly empty tree
        let child_name = "child1__9";
        let (mut fs, _child_ptr) = create_minimal_l2_htree(child_name, fs);

    // WHEN
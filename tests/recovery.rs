use std::{
    fs,
    time::{self, UNIX_EPOCH},
};

use redoxfs::{DiskFile, FileSystem};

#[test]
fn test_recovery() {
    let disk_path = "test_recovery.img";
    let ctime = time::SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap();

    // 1. Create a filesystem and write some data
    {
        let disk = DiskFile::create(disk_path, 1024 * 1024 * 10).unwrap(); // 10 MB
        let mut fs =
            FileSystem::create(disk, None, ctime.as_secs(), ctime.subsec_nanos()).unwrap();

        fs.tx(|tx| {
            let root_ptr = tx.header().tree;
            let a = tx.create_node(root_ptr, "a", 0, 0, 0)?;
            tx.write_node(a.ptr(), 0, b"test", 0, 0)?;
            Ok(())
        })
        .unwrap();

        // Do not unmount, simulating a crash
    }

    // 2. Re-open the filesystem and check for the data
    {
        let disk = DiskFile::open(disk_path).unwrap();
        let mut fs = FileSystem::open(disk, None, None, false).unwrap();

        fs.tx(|tx| {
            let root_ptr = tx.header().tree;
            let a = tx.find_node(root_ptr, "a")?;
            let mut buf = [0; 4];
            tx.read_node(a.ptr(), 0, &mut buf, 0, 0)?;
            assert_eq!(&buf, b"test");
            Ok(())
        })
        .unwrap();
    }

    fs::remove_file(disk_path).unwrap();
}

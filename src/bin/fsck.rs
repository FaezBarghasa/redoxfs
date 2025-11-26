use std::env;
use std::process;

use redoxfs::{DiskFile, FileSystem};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <image>", args[0]);
        process::exit(1);
    }

    let path = &args[1];
    let disk = match DiskFile::open(path) {
        Ok(disk) => disk,
        Err(err) => {
            eprintln!("Failed to open disk: {}", err);
            process::exit(1);
        }
    };

    let mut fs = match FileSystem::open(disk, None, None, false, false) {
        Ok(fs) => fs,
        Err(err) => {
            eprintln!("Failed to open filesystem: {}", err);
            process::exit(1);
        }
    };

    println!("Filesystem open. Checking consistency...");

    let header = fs.header;
    let uuid = header.uuid;
    println!("Header UUID: {:?}", uuid);
    let size = header.size;
    println!("Size: {}", size);

    println!("Scanning blocks...");
    match fs.tx(|tx| tx.scrub_and_repair()) {
        Ok(_) => println!("Scrub complete. No errors found (or repairs successful)."),
        Err(err) => {
            eprintln!("Scrub failed: {}", err);
            process::exit(1);
        }
    }

    println!("Verifying allocator consistency...");
    match fs.tx(|tx| tx.verify_allocator()) {
        Ok(_) => println!("Allocator verification passed."),
        Err(err) => {
            eprintln!("Allocator verification failed: {}", err);
            process::exit(1);
        }
    }
    
    println!("FSCK complete.");
}

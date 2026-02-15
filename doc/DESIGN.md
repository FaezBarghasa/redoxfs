# RedoxFS: Copy-on-Write File System

RedoxFS is the native file system of Redox OS. It is designed from the ground up to provide modern features like data integrity, crash consistency, and high performance in a memory-safe language.

## Design Principles

- **Copy-on-Write (CoW)**: Data is never overwritten in place. Instead, modified data is written to new blocks, and metadata is updated atomically. This provides inherent crash consistency.
- **Checksumming**: All data and metadata are protected by checksums, allowing for the detection and correction of "bit rot."
- **Encryption**: Fully integrated AES-GCM encryption for entire partitions, supported by the Redox bootloader.

## On-Disk Structure

RedoxFS uses a sophisticated H-tree structure to manage inodes and block allocation:

- **Header**: Contains the root of the tree and critical system metadata.
- **Tree Nodes**: Hierarchical nodes that point to either data blocks or further tree nodes.
- **Data Blocks**: The actual file content.

## Transactional Support

Every write operation in RedoxFS is part of a transaction. The filesystem ensures that either the entire transaction succeeds or none of it is applied, making it highly resilient to power failures.

## Performance & Scalability

- Support for up to **4 billion inodes** per partition.
- Max partition size of **193TiB**.
- Efficient allocation algorithms to minimize fragmentation on CoW media.

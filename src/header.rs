
use core::ops::{Deref, DerefMut};
use core::{fmt, mem, slice};
use endian_num::Le;

use aes::Aes128;
use xts_mode::{get_tweak_default, Xts128};

use crate::{AllocList, BlockPtr, KeySlot, QuotaRoot, Tree, BLOCK_SIZE, SIGNATURE, VERSION};

pub const HEADER_RING: u64 = 256;

/// The header of the filesystem.
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct Header {
    /// Signature, should be SIGNATURE
    pub signature: [u8; 8],
    /// Version, should be VERSION
    pub version: Le<u64>,
    /// Disk ID, a 128-bit unique identifier
    pub uuid: [u8; 16],
    /// Disk size, in number of BLOCK_SIZE sectors
    pub size: Le<u64>,
    /// Generation of header
    pub generation: Le<u64>,
    /// Block of first tree node
    pub tree: BlockPtr<Tree>,
    /// Block of last alloc node
    pub alloc: BlockPtr<AllocList>,
    /// Block of snapshot tree root
    pub snapshot_tree_root: BlockPtr<Tree>,
    /// Block of quota table root
    pub quota_table_root: BlockPtr<QuotaRoot>,
    /// Block of refcount table root (New Field)
    pub refcount_table_root: BlockPtr<Tree>,
    /// Key slots
    pub key_slots: [KeySlot; 64],
    /// Padding (Reduced by 32 bytes for refcount_table_root)
    pub padding: [u8; BLOCK_SIZE as usize - 3176 - 96 - 32],
    /// encrypted hash of header data without hash
    pub encrypted_hash: [u8; 16],
    /// hash of header data without hash
    pub hash: Le<u64>,
}

impl Header {
    #[cfg(feature = "std")]
    pub fn new(size: u64) -> Header {
        let uuid = uuid::Uuid::new_v4();
        let mut header = Header {
            signature: *SIGNATURE,
            version: VERSION.into(),
            uuid: *uuid.as_bytes(),
            size: size.into(),
            ..Default::default()
        };
        header.update_hash(None);
        header
    }

    pub fn valid(&self) -> bool {
        if &self.signature != SIGNATURE {
            return false;
        }
        if self.version.to_ne() != VERSION {
            return false;
        }
        if self.hash.to_ne() != self.create_hash() {
            return false;
        }
        true
    }

    pub fn uuid(&self) -> [u8; 16] {
        self.uuid
    }

    pub fn size(&self) -> u64 {
        self.size.to_ne()
    }

    pub fn generation(&self) -> u64 {
        self.generation.to_ne()
    }

    fn create_hash(&self) -> u64 {
        let end = mem::size_of_val(self)
            - mem::size_of_val(&{ self.hash })
            - mem::size_of_val(&{ self.encrypted_hash });
        seahash::hash(&self[..end])
    }

    fn create_encrypted_hash(&self, cipher_opt: Option<&Xts128<Aes128>>) -> [u8; 16] {
        let mut encrypted_hash = [0; 16];
        for (i, b) in self.hash.to_le_bytes().iter().enumerate() {
            encrypted_hash[i] = *b;
        }
        if let Some(cipher) = cipher_opt {
            let mut block = aes::Block::from(encrypted_hash);
            cipher.encrypt_area(
                &mut block,
                BLOCK_SIZE as usize,
                self.generation().into(),
                get_tweak_default,
            );
            encrypted_hash = block.into();
        }
        encrypted_hash
    }

    pub fn encrypted(&self) -> bool {
        (self.encrypted_hash) != self.create_encrypted_hash(None)
    }

    pub fn cipher(&self, password: &[u8]) -> Option<Xts128<Aes128>> {
        let hash = self.create_encrypted_hash(None);
        for slot in self.key_slots.iter() {
            //TODO: handle errors
            if let Ok(cipher) = slot.cipher(password) {
                let mut block = aes::Block::from(self.encrypted_hash);
                cipher.decrypt_area(
                    &mut block,
                    BLOCK_SIZE as usize,
                    self.generation().into(),
                    get_tweak_default,
                );
                if block == aes::Block::from(hash) {
                    return Some(cipher);
                }
            }
        }
        None
    }

    fn update_hash(&mut self, cipher_opt: Option<&Xts128<Aes128>>) {
        self.hash = self.create_hash().into();
        self.encrypted_hash = self.create_encrypted_hash(cipher_opt);
    }

    pub fn update(&mut self, cipher_opt: Option<&Xts128<Aes128>>) -> u64 {
        let mut generation = self.generation();
        generation += 1;
        self.generation = generation.into();
        self.update_hash(cipher_opt);
        generation
    }
}

impl Default for Header {
    fn default() -> Self {
        Self {
            signature: [0; 8],
            version: 0.into(),
            uuid: [0; 16],
            size: 0.into(),
            generation: 0.into(),
            tree: BlockPtr::default(),
            alloc: BlockPtr::default(),
            snapshot_tree_root: BlockPtr::default(),
            quota_table_root: BlockPtr::default(),
            refcount_table_root: BlockPtr::default(),
            key_slots: [KeySlot::default(); 64],
            padding: [0; BLOCK_SIZE as usize - 3176 - 96 - 32],
            encrypted_hash: [0; 16],
            hash: 0.into(),
        }
    }
}

impl fmt::Debug for Header {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Header")
            .field("signature", &self.signature)
            .field("version", &self.version)
            .field("uuid", &self.uuid)
            .field("size", &self.size)
            .field("generation", &self.generation)
            .field("tree", &self.tree)
            .field("alloc", &self.alloc)
            .field("snapshot_tree_root", &self.snapshot_tree_root)
            .field("quota_table_root", &self.quota_table_root)
            .field("refcount_table_root", &self.refcount_table_root)
            .field("hash", &self.hash)
            .finish()
    }
}

impl Deref for Header {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(self as *const Header as *const u8, mem::size_of::<Header>())
                as &[u8]
        }
    }
}

impl DerefMut for Header {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(self as *mut Header as *mut u8, mem::size_of::<Header>())
                as &mut [u8]
        }
    }
}

#[test]
fn header_size_test() {
    assert_eq!(mem::size_of::<Header>(), BLOCK_SIZE as usize);
}
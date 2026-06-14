#![forbid(unsafe_code)]

use zerocopy::{FromBytes, AsBytes, Unaligned};
use core::mem::size_of;

pub const NTFS_ATTR_STANDARD_INFORMATION: u32 = 0x10;
pub const NTFS_ATTR_FILE_NAME: u32 = 0x30;
pub const NTFS_ATTR_DATA: u32 = 0x80;

#[derive(FromBytes, AsBytes, Unaligned, Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct MftRecordHeader {
    pub magic: [u8; 4], // "FILE"
    pub usa_ofs: [u8; 2],
    pub usa_count: [u8; 2],
    pub lsn: [u8; 8],
    pub sequence: [u8; 2],
    pub link_count: [u8; 2],
    pub attrs_offset: [u8; 2],
    pub flags: [u8; 2], // 0x01: InUse, 0x02: Directory
    pub bytes_in_use: [u8; 4],
    pub bytes_allocated: [u8; 4],
    pub base_mft_record: [u8; 8],
    pub next_attr_instance: [u8; 2],
}

impl MftRecordHeader {
    pub fn is_valid(&self) -> bool {
        &self.magic == b"FILE"
    }

    pub fn is_directory(&self) -> bool {
        let flags = u16::from_le_bytes([self.flags[0], self.flags[1]]);
        (flags & 0x02) != 0
    }

    pub fn is_in_use(&self) -> bool {
        let flags = u16::from_le_bytes([self.flags[0], self.flags[1]]);
        (flags & 0x01) != 0
    }
}

#[derive(FromBytes, AsBytes, Unaligned, Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct AttributeHeaderCommon {
    pub attr_type: [u8; 4],
    pub length: [u8; 4],
    pub non_resident: u8,
    pub name_length: u8,
    pub name_offset: [u8; 2],
    pub flags: [u8; 2],
    pub instance: [u8; 2],
}

#[derive(FromBytes, AsBytes, Unaligned, Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct ResidentHeader {
    pub value_length: [u8; 4],
    pub value_offset: [u8; 2],
    pub resident_flags: [u8; 2],
}

#[derive(FromBytes, AsBytes, Unaligned, Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct NonResidentHeader {
    pub lowest_vcn: [u8; 8],
    pub highest_vcn: [u8; 8],
    pub mapping_pairs_offset: [u8; 2],
    pub compression_unit: [u8; 2],
    pub padding: [u8; 4],
    pub allocated_size: [u8; 8],
    pub real_size: [u8; 8],
    pub initialized_size: [u8; 8],
}

pub struct NtfsParser<'a> {
    data: &'a [u8],
}

impl<'a> NtfsParser<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }

    pub fn parse_mft_record(&self) -> Option<(MftRecordHeader, Vec<(&'a AttributeHeaderCommon, &'a [u8])>)> {
        if self.data.len() < size_of::<MftRecordHeader>() {
            return None;
        }

        let record_header = MftRecordHeader::read_from(&self.data[..size_of::<MftRecordHeader>()])?;
        if !record_header.is_valid() {
            return None;
        }

        let mut attributes = Vec::new();
        let attrs_start = u16::from_le_bytes([record_header.attrs_offset[0], record_header.attrs_offset[1]]) as usize;
        let mut offset = attrs_start;

        while offset + size_of::<AttributeHeaderCommon>() <= self.data.len() {
            let type_bytes = &self.data[offset..offset + 4];
            let attr_type = u32::from_le_bytes([type_bytes[0], type_bytes[1], type_bytes[2], type_bytes[3]]);
            if attr_type == 0xFFFFFFFF {
                break; // End of attributes marker
            }

            let attr_common = AttributeHeaderCommon::read_from(&self.data[offset..offset + size_of::<AttributeHeaderCommon>()])?;
            let len = u32::from_le_bytes([
                attr_common.length[0],
                attr_common.length[1],
                attr_common.length[2],
                attr_common.length[3],
            ]) as usize;

            if len == 0 || offset + len > self.data.len() {
                break;
            }

            let attr_data = &self.data[offset..offset + len];
            attributes.push((attr_common, attr_data));
            offset += len;
        }

        Some((record_header, attributes))
    }

    pub fn get_resident_attribute_data(&self, header: &AttributeHeaderCommon, full_attr_data: &'a [u8]) -> Option<&'a [u8]> {
        if header.non_resident != 0 {
            return None; // Non-resident attributes require mapping pairs parsing, not direct resident access
        }

        let header_len = size_of::<AttributeHeaderCommon>() + size_of::<ResidentHeader>();
        if full_attr_data.len() < header_len {
            return None;
        }

        let resident_header = ResidentHeader::read_from(&full_attr_data[size_of::<AttributeHeaderCommon>()..header_len])?;
        let value_offset = u16::from_le_bytes([resident_header.value_offset[0], resident_header.value_offset[1]]) as usize;
        let value_length = u32::from_le_bytes([
            resident_header.value_length[0],
            resident_header.value_length[1],
            resident_header.value_length[2],
            resident_header.value_length[3],
        ]) as usize;

        if value_offset + value_length > full_attr_data.len() {
            return None;
        }

        Some(&full_attr_data[value_offset..value_offset + value_length])
    }
}

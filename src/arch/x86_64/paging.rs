use core::arch::asm;

pub const PAGE_SIZE: usize = 4096;

#[repr(C, align(4096))]
pub struct PagingTable {
    pub entries: [PagingTableEntry; Self::NUM_ENTRIES],
}

impl PagingTable {
    pub const NUM_ENTRIES: usize = 512;

    pub fn new() -> Self {
        Self {
            entries: [PagingTableEntry::empty(); 512],
        }
    }

    pub fn current_pml4() -> *mut Self {
        let pml4_ptr: *mut Self;
        unsafe {
            asm!(
                "mov {}, cr3",
                out(reg) pml4_ptr,
                options(nostack, preserves_flags)
            );
        }
        assert_eq!(pml4_ptr as usize & !4095, pml4_ptr as usize);
        pml4_ptr
    }

    pub fn install(&self) {
        let self_ptr = core::ptr::addr_of!(*self);
        unsafe {
            asm!(
                "mov cr3, {}",
                in(reg) self_ptr,
                options(nostack, preserves_flags)
            );
        }
    }

    pub fn entry(&self, index: usize) -> &PagingTableEntry {
        assert!(index < Self::NUM_ENTRIES);
        &self.entries[index]
    }

    pub fn entry_mut(&mut self, index: usize) -> &mut PagingTableEntry {
        assert!(index < Self::NUM_ENTRIES);
        &mut self.entries[index]
    }
}

impl Default for PagingTable {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct PagingTableEntry {
    opaque: u64,
}

impl PagingTableEntry {
    pub fn empty() -> Self {
        Self { opaque: 0 }
    }

    pub fn is_present(&self) -> bool {
        self.opaque & PageTableEntryFlags::PRESENT == PageTableEntryFlags::PRESENT
    }

    pub fn is_writable(&self) -> bool {
        self.opaque & PageTableEntryFlags::WRITABLE == PageTableEntryFlags::WRITABLE
    }

    pub fn is_user_accessible(&self) -> bool {
        self.opaque & PageTableEntryFlags::USER_ACCESSIBLE == PageTableEntryFlags::USER_ACCESSIBLE
    }

    pub fn addr(&self) -> u64 {
        // addr starts at bit 12, and is 40 bits long for a total of 52 bits of
        // physical addressing
        self.opaque & 0x00FF_FFFF_FFFF_FF00
    }

    pub fn reset(&mut self) {
        self.opaque = 0;
    }

    pub fn load_page(&self) -> *mut u8 {
        self.addr() as *mut u8
    }

    pub fn populate(&mut self, addr: u64) {
        assert!(
            addr as usize % PAGE_SIZE == 0,
            "Addresses must be page-aligned"
        );

        // TODO [matthew-russo 08-10-24] maybe need to check top bits to ensure
        // they conform

        self.opaque = addr | PageTableEntryFlags::PRESENT
    }

    pub fn make_writable(&mut self) {
        self.opaque |= PageTableEntryFlags::WRITABLE;
    }

    pub fn make_user_accessible(&mut self) {
        self.opaque |= PageTableEntryFlags::USER_ACCESSIBLE;
    }

    pub fn disable_caching(&mut self) {
        self.opaque |= PageTableEntryFlags::DISABLE_CACHING;
    }
}

impl core::fmt::Debug for PagingTableEntry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("PagingTableEntry")
            .field("present", &self.is_present())
            .field("writable", &self.is_writable())
            .field("user_accessible", &self.is_user_accessible())
            .field("addr", &self.addr())
            .field("raw", &self.opaque)
            .finish()
    }
}

pub struct PageTableEntryFlags {}

impl PageTableEntryFlags {
    pub const PRESENT: u64 = 0b00000001;
    pub const WRITABLE: u64 = 0b00000010;
    pub const USER_ACCESSIBLE: u64 = 0b00000100;
    pub const ENABLE_WRITE_THROUGH_CACHING: u64 = 0b00001000;
    pub const DISABLE_CACHING: u64 = 0b00010000;
    pub const ACCESSED: u64 = 0b00100000;
    pub const HUGE_PAGES: u64 = 0b10000000;
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct PagingTableIndices {
    pub pml4_index: usize,
    pub pdpt_index: usize,
    pub pd_index: usize,
    pub pt_index: usize,
}

// 0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111
//
// 0b11111111_11111111 | 11111111_1 | 1111111_11 | 111111_111 | 11111_1111 |
// 1111_11111111
//
//        unused            pml4         pdpt          pd           pt
// offset 0b11111111_11111111 | 11111111_1 | 1111111_11 | 111111_111 |
// 11111_1111 | 1111_11111111
impl From<u64> for PagingTableIndices {
    fn from(mut addr: u64) -> Self {
        // ditch the offset
        addr >>= 12;

        let pt_index = lowest_9_bits(addr) as usize;
        addr >>= 9;

        let pd_index = lowest_9_bits(addr) as usize;
        addr >>= 9;

        let pdpt_index = lowest_9_bits(addr) as usize;
        addr >>= 9;

        let pml4_index = lowest_9_bits(addr) as usize;

        Self {
            pml4_index,
            pdpt_index,
            pd_index,
            pt_index,
        }
    }
}

fn lowest_9_bits(addr: u64) -> u64 {
    addr & 0b1_1111_1111
}

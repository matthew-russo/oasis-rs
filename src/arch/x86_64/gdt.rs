use crate::arch::x86_64::tss::TaskStateSegment;

// TODO [matthew-russo 08-10-24] don't hard-code num entries and leave it up to
// the caller.
#[repr(C, align(16))]
pub struct GlobalDescriptorTable {
    entries: [GlobalDescriptor; 9],
}

impl GlobalDescriptorTable {
    pub fn with_tss(tss: &'static TaskStateSegment) -> Self {
        let (tss_lo, tss_hi) = GlobalDescriptor::for_tss(tss);
        Self {
            entries: [
                GlobalDescriptor::NULL,
                GlobalDescriptor::KERNEL_DATA,
                GlobalDescriptor::KERNEL_32_BIT_CODE,
                GlobalDescriptor::KERNEL_64_BIT_CODE,
                GlobalDescriptor::USER_DATA,
                GlobalDescriptor::USER_32_BIT_CODE,
                GlobalDescriptor::USER_64_BIT_CODE,
                tss_lo,
                tss_hi,
            ],
        }
    }

    pub fn install(&self) {
        #[repr(C, packed)]
        struct Gdtr {
            size: u16,
            offset: u64,
        }
        let self_ptr = core::ptr::addr_of!(*self);
        let gdtr = Gdtr {
            size: (core::mem::size_of::<Self>() - 1) as u16,
            offset: self_ptr as u64,
        };
        unsafe {
            core::arch::asm!(
                "lgdt [{}]",
                in(reg) &gdtr,
                options(nostack)
            );
        }
    }

    pub fn update_registers(code_selector: SegmentSelector, data_selector: SegmentSelector) {
        Self::update_code_segment(code_selector);
        Self::update_non_code_segments(data_selector);
    }

    pub fn kernel_64_bit_data_selector() -> SegmentSelector {
        SegmentSelector::global_ring_0(1)
    }

    pub fn kernel_64_bit_code_selector() -> SegmentSelector {
        SegmentSelector::global_ring_0(3)
    }

    pub fn user_64_bit_data_selector() -> SegmentSelector {
        SegmentSelector::global_ring_3(4)
    }

    pub fn user_64_bit_code_selector() -> SegmentSelector {
        SegmentSelector::global_ring_3(6)
    }

    pub(crate) fn tss_selector() -> SegmentSelector {
        SegmentSelector(7 << 3)
    }

    #[allow(binary_asm_labels)]
    fn update_code_segment(code_selector: SegmentSelector) {
        unsafe {
            // set the CS register by using a far return. we first push
            // the segment selector, then load the instruction pointer and
            // push it to the stack as well, then far return
            core::arch::asm!(
                "push {sel}",
                "lea {tmp}, [1f + rip]",
                "push {tmp}",
                "retfq",
                "1:",
                sel = in(reg) u16::from(code_selector) as u64,
                tmp = lateout(reg) _,
                options(preserves_flags),
            );
        }
    }

    pub fn update_non_code_segments(data_selector: SegmentSelector) {
        unsafe {
            // set all other segment registers with the provided data_selector
            core::arch::asm!(
                "mov rax, {sel}",
                "mov ds, ax",
                "mov es, ax",
                "mov fs, ax",
                "mov gs, ax",
                "mov ss, ax",
                sel = in(reg) u16::from(data_selector) as u64,
                options(preserves_flags),
            );
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct GlobalDescriptor(u64);

impl GlobalDescriptor {
    const NULL: Self = Self(0);

    pub const KERNEL_DATA: Self =
        Self(GlobalDescriptorBits::COMMON_NON_SYSTEM | GlobalDescriptorBits::SIZE_32_BIT_SEGMENT);
    pub const KERNEL_32_BIT_CODE: Self = Self(
        GlobalDescriptorBits::COMMON_NON_SYSTEM
            | GlobalDescriptorBits::EXECUTABLE
            | GlobalDescriptorBits::SIZE_32_BIT_SEGMENT,
    );
    pub const KERNEL_64_BIT_CODE: Self = Self(
        GlobalDescriptorBits::COMMON_NON_SYSTEM
            | GlobalDescriptorBits::EXECUTABLE
            | GlobalDescriptorBits::LONG_MODE,
    );

    pub const USER_DATA: Self = Self(
        GlobalDescriptorBits::COMMON_NON_SYSTEM
            | GlobalDescriptorBits::RING_3
            | GlobalDescriptorBits::SIZE_32_BIT_SEGMENT,
    );
    pub const USER_32_BIT_CODE: Self = Self(
        GlobalDescriptorBits::COMMON_NON_SYSTEM
            | GlobalDescriptorBits::RING_3
            | GlobalDescriptorBits::EXECUTABLE
            | GlobalDescriptorBits::SIZE_32_BIT_SEGMENT,
    );
    pub const USER_64_BIT_CODE: Self = Self(
        GlobalDescriptorBits::COMMON_NON_SYSTEM
            | GlobalDescriptorBits::RING_3
            | GlobalDescriptorBits::EXECUTABLE
            | GlobalDescriptorBits::LONG_MODE,
    );

    pub fn for_tss(tss: &'static TaskStateSegment) -> (Self, Self) {
        let mut lo: u64 = 0;
        let mut hi: u64 = 0;

        let tss_addr = tss as *const _ as u64;

        // set the various address ranges
        lo |= ((tss_addr as u16) as u64) << 16;
        lo |= (((tss_addr >> 16) as u8) as u64) << 32;
        lo |= (((tss_addr >> 24) as u8) as u64) << 56;
        hi |= tss_addr >> 32;

        // set the descriptor type in the access byte
        lo |= GlobalDescriptorBits::TSS_AVAILABLE_64_BIT_TY;

        // set the limit (size of the tss)
        lo |= ((core::mem::size_of::<TaskStateSegment>() - 1) as u16) as u64;

        (Self(lo), Self(hi))
    }
}

struct GlobalDescriptorBits;
impl GlobalDescriptorBits {
    // Not used in 64 bit mode
    const LIMIT_0_15: u64 = 0xFFFF;
    const LIMIT_16_19: u64 = 0xF << 48;

    const PRESENT: u64 = 1 << 47;

    const RING_3: u64 = 3 << 45;

    const NON_SYSTEM_SEGMENT: u64 = 1 << 44;

    const EXECUTABLE: u64 = 1 << 43;

    const WRITABLE: u64 = 1 << 41;

    const ACCESSED: u64 = 1 << 40;

    const PAGE_GRANULARITY: u64 = 1 << 55;

    const SIZE_32_BIT_SEGMENT: u64 = 1 << 54;

    const LONG_MODE: u64 = 1 << 53;

    const COMMON_NON_SYSTEM: u64 = Self::LIMIT_0_15
        | Self::LIMIT_16_19
        | Self::PRESENT
        | Self::NON_SYSTEM_SEGMENT
        | Self::WRITABLE
        | Self::ACCESSED
        | Self::PAGE_GRANULARITY;

    // const TSS_AVAILABLE_64_BIT_TY: u64 = 0b11101001 << 40;
    const TSS_AVAILABLE_64_BIT_TY: u64 = 0b10001001 << 40;
}

#[repr(transparent)]
pub struct SegmentSelector(u16);

impl From<SegmentSelector> for u16 {
    fn from(selector: SegmentSelector) -> u16 {
        selector.0
    }
}

impl SegmentSelector {
    pub fn global_ring_0(entry: u16) -> Self {
        Self(entry << 3)
    }

    pub fn local_ring_0(entry: u16) -> Self {
        Self((entry << 3) | (1 << 2))
    }

    pub fn global_ring_3(entry: u16) -> Self {
        Self((entry << 3) | 3)
    }

    pub fn local_ring_3(entry: u16) -> Self {
        Self((entry << 3) | (1 << 2) | 3)
    }
}

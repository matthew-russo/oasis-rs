#[repr(C, align(16))]
#[derive(Clone, Debug)]
pub struct InterruptDescriptorTable {
    entries: [InterruptDescriptor; 256],
}

#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct Idtr {
    size: u16,
    offset: u64,
}

impl Idtr {
    fn invalid() -> Self {
        Self { size: 0, offset: 0 }
    }
}

impl InterruptDescriptorTable {
    pub fn new() -> Self {
        Self {
            entries: [InterruptDescriptor::empty(); 256],
        }
    }

    pub fn load() -> Self {
        let idtr: Idtr = Idtr::invalid();

        unsafe {
            core::arch::asm!(
                "sidt [{}]",
                in(reg) &idtr,
                options(nostack)
            );
        }

        assert_ne!(idtr, Idtr::invalid());
        let idt_ptr = idtr.offset as *const Self;
        unsafe { (*idt_ptr).clone() }
    }

    pub fn install(&self) {
        let self_ptr = core::ptr::addr_of!(*self);
        let idtr = Idtr {
            size: (core::mem::size_of::<Self>() - 1) as u16,
            offset: self_ptr as u64,
        };
        unsafe {
            core::arch::asm!(
                "lidt [{}]",
                in(reg) &idtr,
                options(nostack)
            );
        }
    }

    pub fn set_handler(&mut self, vector: usize, addr: HandlerFuncAddr) {
        self.entries[vector] = InterruptDescriptor::from(addr);
    }

    pub fn set_divide_error_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(0, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_debug_exception_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(1, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_nmi_interrupt_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(2, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_breakpoint_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(3, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_overflow_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(4, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_bound_range_exceeded_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(5, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_invalid_opcode_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(6, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_device_not_available_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(7, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_double_fault_handler(
        &mut self,
        handler: DivergingInterruptServiceRoutineWithErrorCode,
    ) {
        self.set_handler(8, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_coprocessor_segment_overrun_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(9, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_invalid_tss_handler(&mut self, handler: InterruptServiceRoutineWithErrorCode) {
        self.set_handler(10, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_segment_not_present_handler(
        &mut self,
        handler: InterruptServiceRoutineWithErrorCode,
    ) {
        self.set_handler(11, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_stack_segment_fault_handler(
        &mut self,
        handler: InterruptServiceRoutineWithErrorCode,
    ) {
        self.set_handler(12, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_general_protection_handler(
        &mut self,
        handler: InterruptServiceRoutineWithErrorCode,
    ) {
        self.set_handler(13, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_page_fault_handler(&mut self, handler: InterruptServiceRoutineWithErrorCode) {
        self.set_handler(14, HandlerFuncAddr::from(handler as usize));
    }

    // 15 — Intel reserved. Do not use.
    // https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3a-part-1-manual.pdf

    pub fn set_x87_fpu_floating_point_error_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(16, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_alignment_check_handler(&mut self, handler: InterruptServiceRoutineWithErrorCode) {
        self.set_handler(17, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_machine_check_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(18, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_simd_floating_point_exception_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(19, HandlerFuncAddr::from(handler as usize));
    }

    pub fn set_virtualization_exception_handler(&mut self, handler: InterruptServiceRoutine) {
        self.set_handler(20, HandlerFuncAddr::from(handler as usize));
    }

    // 21-31 — Intel reserved. Do not use.
    // https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3a-part-1-manual.pdf

    // 32-255 — User Defined (Non-reserved) Interrupts
    // https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3a-part-1-manual.pdf
}

impl Default for InterruptDescriptorTable {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct InterruptDescriptor {
    lower_16_fn_addr: u16,
    segment_selector: u16,
    // 0-2	Interrupt Stack Table Index	0: Don’t switch stacks, 1-7: Switch to the n-th stack in the
    // Interrupt Stack Table when this handler is called. 3-7	Reserved
    // 8	0: Interrupt Gate, 1: Trap Gate	If this bit is 0, interrupts are disabled when this handler
    // is called. 9-11	must be one
    // 12	must be zero
    // 13‑14	Descriptor Privilege Level (DPL)	The minimal privilege level required for calling this
    // handler. 15	Present
    flags: u16,
    middle_16_fn_addr: u16,
    upper_32_fn_addr: u32,
    reserved: u32,
}

impl InterruptDescriptor {
    pub fn empty() -> Self {
        Self {
            lower_16_fn_addr: 0,
            segment_selector: 0,
            flags: 0,
            middle_16_fn_addr: 0,
            upper_32_fn_addr: 0,
            reserved: 0,
        }
    }

    pub fn reset(&mut self) {
        *self = Self::empty();
    }
}

struct InterruptDescriptorFlags {}
impl InterruptDescriptorFlags {
    const PRESENT: u16 = 0b1000_0000_0000_0000;
    #[allow(dead_code)]
    const RING_0: u16 = 0b0000_0000_0000_0000;
    #[allow(dead_code)]
    const RING_1: u16 = 0b0010_0000_0000_0000;
    #[allow(dead_code)]
    const RING_2: u16 = 0b0100_0000_0000_0000;
    #[allow(dead_code)]
    const RING_3: u16 = 0b0110_0000_0000_0000;
    const INTERRUPT_GATE: u16 = 0b0000_1110_0000_0000;
}

impl From<HandlerFuncAddr> for InterruptDescriptor {
    fn from(addr: HandlerFuncAddr) -> Self {
        let addr = addr.0;
        Self {
            lower_16_fn_addr: addr as u16,
            // TODO [matthew-russo 08-10-24] Shouldn't be hardcoded
            segment_selector:
                crate::arch::x86_64::gdt::GlobalDescriptorTable::kernel_64_bit_code_selector()
                    .into(),
            flags: InterruptDescriptorFlags::PRESENT
                | InterruptDescriptorFlags::INTERRUPT_GATE
                | InterruptDescriptorFlags::RING_3,
            middle_16_fn_addr: (addr >> 16) as u16,
            upper_32_fn_addr: (addr >> 32) as u32,
            reserved: 0,
        }
    }
}

#[repr(C)]
pub struct InterruptStackFrame {
    /// This value points to the instruction that should be executed when the
    /// interrupt handler returns. For most interrupts, this value points to
    /// the instruction immediately following the last executed instruction.
    /// However, for some exceptions (e.g., page faults), this value points
    /// to the faulting instruction, so that the instruction is restarted on
    /// return. See the documentation of the [`InterruptDescriptorTable`] fields
    /// for more details.
    pub instruction_pointer: u64,
    /// The code segment selector, padded with zeros.
    pub code_segment: u64,
    /// The flags register before the interrupt handler was invoked.
    pub cpu_flags: u64,
    /// The stack pointer at the time of the interrupt.
    pub stack_pointer: u64,
    /// The stack segment descriptor at the time of the interrupt (often zero in
    /// 64-bit mode).
    pub stack_segment: u64,
}

impl core::fmt::Debug for InterruptStackFrame {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("InterruptStackFrame")
            .field(
                "instruction_pointer",
                &core::format_args!("{:x}", &self.instruction_pointer),
            )
            .field("code_segment", &self.code_segment)
            .field("cpu_flags", &core::format_args!("{:b}", &self.cpu_flags))
            .field(
                "stack_pointer",
                &core::format_args!("{:x}", &self.stack_pointer),
            )
            .field("stack_segment", &self.stack_segment)
            .finish()
    }
}

pub struct HandlerFuncAddr(usize);

impl From<usize> for HandlerFuncAddr {
    fn from(addr: usize) -> Self {
        Self(addr)
    }
}

pub type InterruptServiceRoutine = extern "x86-interrupt" fn(InterruptStackFrame);
pub type InterruptServiceRoutineWithErrorCode = extern "x86-interrupt" fn(InterruptStackFrame, u64);
pub type DivergingInterruptServiceRoutineWithErrorCode =
    extern "x86-interrupt" fn(InterruptStackFrame, u64) -> !;

// 31              15                             4               0
// +--------------+-----+--------------+----+----+---+---+---+---+---+
// |   Reserved   | SGX |   Reserved   | SS | PK | I | R | U | W | P |
// +--------------+-----+--------------+----+----+---+---+---+---+---+
//
// 	Length 	Name 	Description
// P 	1 bit 	Present 	When set, the page fault was caused by a page-protection violation. When not set, it was caused by a non-present page.
// W 	1 bit 	Write 	When set, the page fault was caused by a write access. When not set, it was caused by a read access.
// U 	1 bit 	User 	When set, the page fault was caused while CPL = 3. This does not necessarily mean that the page fault was a privilege violation.
// R 	1 bit 	Reserved write 	When set, one or more page directory entries contain reserved bits which are set to 1. This only applies when the PSE or PAE flags in CR4 are set to 1.
// I 	1 bit 	Instruction Fetch 	When set, the page fault was caused by an instruction fetch. This only applies when the No-Execute bit is supported and enabled.
// PK 	1 bit 	Protection key 	When set, the page fault was caused by a protection-key violation. The PKRU register (for user-mode accesses) or PKRS MSR (for supervisor-mode accesses) specifies the protection key rights.
// SS 	1 bit 	Shadow stack 	When set, the page fault was caused by a shadow stack access.
// SGX 	1 bit 	Software Guard Extensions 	When set, the fault was due to an SGX violation. The fault is unrelated to ordinary paging.

#[derive(Debug)]
pub enum PagePresentErrorReasoning {
    PresentPageProtectionViolation,
    NotPresent,
}

impl Default for PagePresentErrorReasoning {
    fn default() -> Self {
        Self::NotPresent
    }
}

#[derive(Debug, Default)]
pub struct PageFaultErrorCode {
    present: PagePresentErrorReasoning,
    write_access: bool,
    user: bool,
    reserved: bool,
    instruction_fetch: bool,
    protection_key: bool,
    shadow_stack: bool,
    software_guard_extension: bool,
}

impl PageFaultErrorCode {
    const PRESENT_BIT: usize = 0;
    const WRITE_ACCESS_BIT: usize = 1;
    const USER_BIT: usize = 2;
    const RESERVED_BIT: usize = 3;
    const INSTRUCTION_FETCH_BIT: usize = 4;
    const PROTECTION_KEY_BIT: usize = 5;
    const SHADOW_STACK_BIT: usize = 6;
    const SGK_BIT: usize = 15;
}

impl From<u64> for PageFaultErrorCode {
    fn from(raw: u64) -> Self {
        let mut pfec = PageFaultErrorCode::default();

        if raw & (0b1 << Self::PRESENT_BIT) == (0b1 << Self::PRESENT_BIT) {
            pfec.present = PagePresentErrorReasoning::PresentPageProtectionViolation;
        }

        if raw & (0b1 << Self::WRITE_ACCESS_BIT) == (0b1 << Self::WRITE_ACCESS_BIT) {
            pfec.write_access = true;
        }

        if raw & (0b1 << Self::USER_BIT) == (0b1 << Self::USER_BIT) {
            pfec.user = true;
        }

        if raw & (0b1 << Self::RESERVED_BIT) == (0b1 << Self::RESERVED_BIT) {
            pfec.reserved = true;
        }

        if raw & (0b1 << Self::INSTRUCTION_FETCH_BIT) == (0b1 << Self::INSTRUCTION_FETCH_BIT) {
            pfec.instruction_fetch = true;
        }

        if raw & (0b1 << Self::PROTECTION_KEY_BIT) == (0b1 << Self::PROTECTION_KEY_BIT) {
            pfec.protection_key = true;
        }

        if raw & (0b1 << Self::SHADOW_STACK_BIT) == (0b1 << Self::SHADOW_STACK_BIT) {
            pfec.shadow_stack = true;
        }

        if raw & (0b1 << Self::SGK_BIT) == (0b1 << Self::SGK_BIT) {
            pfec.software_guard_extension = true;
        }

        pfec
    }
}

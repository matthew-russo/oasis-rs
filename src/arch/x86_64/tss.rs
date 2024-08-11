use crate::arch::x86_64::gdt::GlobalDescriptorTable;

pub enum PrivilegeLevel {
    Ring0,
    Ring1,
    Ring2,
}

#[repr(C, packed(4))]
pub struct TaskStateSegment {
    _reserved_1: u32,
    pst: [u64; 3],
    _reserved_2: u64,
    ist: [u64; 7],
    _reserved_3: u64,
    _reserved_4: u16,
    iopb: u16,
}

const _: () = assert!(core::mem::size_of::<TaskStateSegment>() == 104);

impl TaskStateSegment {
    pub fn new() -> Self {
        Self {
            _reserved_1: 0,
            pst: [0; 3],
            _reserved_2: 0,
            ist: [0; 7],
            _reserved_3: 0,
            _reserved_4: 0,
            iopb: core::mem::size_of::<TaskStateSegment>() as u16,
        }
    }

    pub fn set_privileged_stack(&mut self, privilege_level: PrivilegeLevel, rsp: u64) {
        match privilege_level {
            PrivilegeLevel::Ring0 => self.pst[0] = rsp,
            PrivilegeLevel::Ring1 => self.pst[1] = rsp,
            PrivilegeLevel::Ring2 => self.pst[2] = rsp,
        }
    }

    pub fn install() {
        unsafe {
            core::arch::asm!(
                "ltr {0:x}",
                in(reg) u16::from(GlobalDescriptorTable::tss_selector()),
                options(nostack)
            );
        }
    }
}

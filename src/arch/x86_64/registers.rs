macro_rules! define_register_getter {
    ($reg:ident) => {
        pub fn $reg() -> u64 {
            let $reg: u64;
            unsafe {
                core::arch::asm!(
                    concat!("mov {}, ", stringify!($reg), ";"),
                    out(reg) $reg,
                    options(nostack)
                );
            }
            $reg
        }
    };
}

pub fn rip() -> u64 {
    let rip: u64;
    unsafe {
        core::arch::asm!(
            "lea {}, [rip]",
            out(reg) rip,
        );
    }
    rip
}

define_register_getter!(cr3);
define_register_getter!(rbp);
define_register_getter!(rsp);
define_register_getter!(rsi);
define_register_getter!(rdi);
define_register_getter!(rax);
define_register_getter!(rbx);
define_register_getter!(rcx);
define_register_getter!(rdx);
define_register_getter!(r8);
define_register_getter!(r9);
define_register_getter!(r10);
define_register_getter!(r11);
define_register_getter!(r12);
define_register_getter!(r13);
define_register_getter!(r14);
define_register_getter!(r15);

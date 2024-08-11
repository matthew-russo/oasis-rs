#![cfg(target_arch = "x86_64")]

pub mod cpuid;
pub mod gdt;
pub mod idt;
pub mod io;
pub mod paging;
pub mod registers;
pub mod tss;

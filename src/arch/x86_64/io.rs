#[repr(C)]
pub enum Port {
    Pic1Command = 0x20,
    Pic1Data = 0x21,
    Pic2Command = 0xa0,
    Pic2Data = 0xa1,
    Ps2ControllerData = 0x60,
    Ps2ControllerCommand = 0x64,
    PciConfigAddress = 0xCF8,
    PciConfigData = 0xCFC,
    Unused = 0x80,
}

pub fn inb(port: Port) -> u8 {
    let result: u8;
    unsafe {
        core::arch::asm!(
            "in al, dx",
            out("al") result,
            in("dx") port as u16,
        );
    }
    result
}

pub fn outb(port: Port, b: u8) {
    unsafe {
        core::arch::asm!(
            "out dx, al",
            in("dx") port as u16,
            in("al") b,
        );
    }
}

pub fn inw(port: Port) -> u16 {
    let result: u16;
    unsafe {
        core::arch::asm!(
            "in ax, dx",
            out("ax") result,
            in("dx") port as u16,
        );
    }
    result
}

pub fn outw(port: Port, b: u16) {
    unsafe {
        core::arch::asm!(
            "out dx, ax",
            in("dx") port as u16,
            in("ax") b,
        );
    }
}

pub fn inl(port: Port) -> u32 {
    let result: u32;
    unsafe {
        core::arch::asm!(
            "in eax, dx",
            out("eax") result,
            in("dx") port as u16,
        );
    }
    result
}

pub fn outl(port: Port, b: u32) {
    unsafe {
        core::arch::asm!(
            "out dx, eax",
            in("dx") port as u16,
            in("eax") b,
        );
    }
}

pub fn wait() {
    outb(Port::Unused, 0);
}

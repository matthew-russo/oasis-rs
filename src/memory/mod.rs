#![cfg_attr(feature = "no-std", no_std)]

pub mod alloc;
pub mod memory_map;

/// a memory location in the physical address space
#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PhysicalAddress(usize);

impl core::fmt::Debug for PhysicalAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("PhysicalAddress")
            .field("addr", &core::format_args!("{:x}", &self.0))
            .finish()
    }
}

impl PhysicalAddress {
    /// construct a new PhysicalAddress
    pub fn new(phys_addr: usize) -> Self {
        Self(phys_addr)
    }

    /// get a new PhysicalAddress, offset by the provided amount
    pub fn offset(&self, offset: usize) -> Self {
        Self(self.0 + offset)
    }

    /// get the raw memory location
    pub fn into_inner(&self) -> usize {
        self.0
    }

    /// convert this PhysicalAddress into a VirtualAddress by applying an offset
    pub fn get_virt_addr<const PHYS_TO_VIRT_OFFSET: usize>(&self) -> VirtualAddress {
        VirtualAddress(self.0 + PHYS_TO_VIRT_OFFSET)
    }
}

/// a memory location in the virtual address space
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct VirtualAddress(usize);

impl VirtualAddress {
    /// construct a new VirtualAddress
    pub fn new(addr: usize) -> Self {
        Self(addr)
    }

    /// get a new VirtualAddress, offset by the provided amount
    pub fn offset(&self, offset: usize) -> Self {
        Self(self.0 + offset)
    }

    /// get the raw memory location
    pub fn into_inner(&self) -> usize {
        self.0
    }

    /// convert the address in to an immutable pointer
    pub fn as_ptr<T>(&self) -> *const T {
        self.0 as *const T
    }

    /// convert the address in to a mutable pointer
    pub fn as_ptr_mut<T>(&self) -> *mut T {
        self.0 as *mut T
    }
}

/// a MemoryDefinition describes what physical memory is available
pub trait MemoryDefinition {
    type FreeFrameIter<'a>: Iterator<Item = PhysicalAddress> + DoubleEndedIterator
    where
        Self: 'a;

    /// returns a double-ended iterator of locations in physical memory. each
    /// address in the iterator is the beginning of a `frame_size` chunk of memory
    /// that is available to use
    fn free_frames(&self, frame_size: usize) -> Self::FreeFrameIter<'_>;
}

#[cfg(target_arch = "x86_64")]
pub const fn assert_page_aligned(n: usize) {
    if align_to_page(n) != n {
        panic!("Value not page aligned");
    }
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub const fn align_to_page(addr: usize) -> usize {
    (addr + (crate::arch::x86_64::paging::PAGE_SIZE - 1))
        & !(crate::arch::x86_64::paging::PAGE_SIZE - 1)
}

#[cfg(test)]
mod test_utils {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    #[repr(C, align(4096))]
    pub struct BufferMemory<const SIZE: usize> {
        buffer: [u8; SIZE],
    }

    impl<const SIZE: usize> BufferMemory<SIZE> {
        pub fn new() -> Self {
            Self { buffer: [0; SIZE] }
        }

        pub fn buffer(&self) -> &[u8] {
            &self.buffer
        }
    }

    pub struct BufferMemoryFrameIter<'a, const SIZE: usize> {
        mem: &'a BufferMemory<SIZE>,
        frame_size: usize,
        front_offset: usize,
        back_offset: usize,
    }

    impl<'a, const SIZE: usize> Iterator for BufferMemoryFrameIter<'a, SIZE> {
        type Item = PhysicalAddress;

        fn next(&mut self) -> Option<Self::Item> {
            if self.front_offset >= self.back_offset {
                return None;
            }

            if self.front_offset + self.frame_size >= self.mem.buffer.len() {
                return None;
            }

            let mem_start = core::ptr::addr_of!(*self.mem);
            let curr_offset = mem_start as usize + self.front_offset;
            self.front_offset += self.frame_size;
            Some(PhysicalAddress::new(curr_offset))
        }
    }

    impl<'a, const SIZE: usize> DoubleEndedIterator for BufferMemoryFrameIter<'a, SIZE> {
        fn next_back(&mut self) -> Option<Self::Item> {
            if self.front_offset >= self.back_offset {
                return None;
            }

            if self.front_offset + self.frame_size >= self.mem.buffer.len() {
                return None;
            }

            let mem_start = core::ptr::addr_of!(*self.mem);
            let curr_offset = mem_start as usize + self.back_offset;
            self.back_offset -= self.frame_size;
            Some(PhysicalAddress::new(curr_offset))
        }
    }

    impl<const SIZE: usize> MemoryDefinition for BufferMemory<SIZE> {
        type FreeFrameIter<'a> = BufferMemoryFrameIter<'a, SIZE>;

        fn free_frames<'a>(&'a self, frame_size: usize) -> Self::FreeFrameIter<'a> {
            if frame_size > self.buffer.len() {
                panic!(
                    "Memory buffer is only {} bytes long but frame size of {} was requested",
                    self.buffer.len(),
                    frame_size,
                );
            }

            BufferMemoryFrameIter {
                mem: self,
                frame_size,
                front_offset: 0,
                back_offset: self.buffer.len() - frame_size,
            }
        }
    }
}

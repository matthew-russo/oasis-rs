#![cfg(target_arch = "x86_64")]

use crate::arch::x86_64::paging::{PagingTable, PagingTableIndices, PAGE_SIZE};
use crate::memory::PhysicalAddress;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryMutability {
    ReadWrite,
    Read,
}

pub struct VirtualMapping {
    pub cacheable: bool,
    pub mutability: MemoryMutability,
    pub phys: usize,
    pub virt: usize,
    pub size: usize,
}

impl VirtualMapping {
    fn address_ranges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        use core::iter::successors;

        successors(Some(self.phys), |p| Some(p + PAGE_SIZE))
            .take_while(|i| *i < self.phys + self.size)
            .zip(
                successors(Some(self.virt), |v| Some(v + PAGE_SIZE))
                    .take_while(|i| *i < self.virt + self.size),
            )
    }
}

impl core::fmt::Debug for VirtualMapping {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("VirtualMapping")
            .field("mutability", &self.mutability)
            .field("phys", &format_args!("{:X}", self.phys))
            .field("virt", &format_args!("{:X}", self.virt))
            .field("size", &format_args!("{:X}", self.size))
            .finish()
    }
}

pub struct VirtualMapper<'a> {
    allocator: &'a crate::memory::alloc::PhysicalMemoryAllocator,
}

impl<'a> VirtualMapper<'a> {
    pub fn new(allocator: &'a crate::memory::alloc::PhysicalMemoryAllocator) -> Self {
        Self { allocator }
    }

    pub fn map<const PHYS_TO_VIRT_OFFSET: usize>(
        &self,
        pml4: *mut PagingTable,
        virt_mapping: &VirtualMapping,
    ) {
        crate::memory::assert_page_aligned(virt_mapping.phys);
        crate::memory::assert_page_aligned(virt_mapping.virt);
        crate::memory::assert_page_aligned(virt_mapping.size);

        for (phys_addr, virt_addr) in virt_mapping.address_ranges() {
            let table_indices = PagingTableIndices::from(virt_addr as u64);

            // for each intermediate index, resolve the next table
            let pt = [
                table_indices.pml4_index,
                table_indices.pdpt_index,
                table_indices.pd_index,
            ]
            .into_iter()
            .fold(pml4, |curr_table, index| {
                self.get_or_allocate_table_entry::<PHYS_TO_VIRT_OFFSET>(
                    curr_table,
                    index,
                    virt_mapping.mutability,
                )
            });

            // now that we have the final page table, make sure an entry isn't
            // present and populate the mapping, making it mutable if necessary
            let pt_entry = unsafe { (*pt).entry_mut(table_indices.pt_index) };
            // assert!(!pt_entry.is_present(), "overwriting an existing memory mapping");
            pt_entry.populate(phys_addr as u64);
            pt_entry.make_user_accessible();
            if let MemoryMutability::ReadWrite = virt_mapping.mutability {
                pt_entry.make_writable();
            }
            if !virt_mapping.cacheable {
                pt_entry.disable_caching();
            }
        }
    }

    fn get_or_allocate_table_entry<const PHYS_TO_VIRT_OFFSET: usize>(
        &self,
        table: *mut PagingTable,
        index: usize,
        mutability: MemoryMutability,
    ) -> *mut PagingTable {
        let entry = unsafe { (*table).entry_mut(index) };
        if !entry.is_present() {
            let entry_phys_addr = self.allocator.alloc_frame().expect("oom");
            let entry_ptr = entry_phys_addr
                .get_virt_addr::<PHYS_TO_VIRT_OFFSET>()
                .as_ptr_mut();
            unsafe {
                *entry_ptr = PagingTable::new();
            }
            entry.populate(entry_phys_addr.into_inner() as u64);
            entry.make_user_accessible();
            if let MemoryMutability::ReadWrite = mutability {
                entry.make_writable();
            }
        }
        PhysicalAddress::new(entry.load_page() as usize)
            .get_virt_addr::<PHYS_TO_VIRT_OFFSET>()
            .as_ptr_mut()
    }
}

pub fn page_bounds(start: usize, end: usize) -> (usize, usize) {
    let lower_bound = start / PAGE_SIZE * PAGE_SIZE;
    let upper_bound = if end % PAGE_SIZE == 0 {
        end
    } else {
        (end / PAGE_SIZE + 1) * PAGE_SIZE
    };
    (lower_bound, upper_bound)
}

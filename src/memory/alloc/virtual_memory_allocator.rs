#![cfg(target_arch = "x86_64")]

use crate::arch::x86_64::paging::PagingTable;
use crate::collections::linked_list::{LinkedList, LinkedListNode};
use crate::memory::alloc::virtual_memory_mapper::{
    MemoryMutability, VirtualMapper, VirtualMapping,
};
use crate::memory::alloc::{Chunk, PhysicalMemoryAllocator, Pool, FRAME_SIZE};
use crate::memory::{PhysicalAddress, VirtualAddress};

use core::mem::MaybeUninit;

pub struct VirtualMemoryAllocator<const PHYS_TO_VIRT_OFFSET: usize> {
    frame_allocator: &'static PhysicalMemoryAllocator,
    virtual_address_tracker: VirtualAddressTracker<PHYS_TO_VIRT_OFFSET>,
}

impl<const PHYS_TO_VIRT_OFFSET: usize> VirtualMemoryAllocator<PHYS_TO_VIRT_OFFSET> {
    pub fn new(frame_allocator: &'static PhysicalMemoryAllocator) -> Self {
        let virtual_address_tracker = VirtualAddressTracker::new(frame_allocator);
        Self {
            frame_allocator,
            virtual_address_tracker,
        }
    }

    pub fn allocate(&mut self, size: usize) -> Option<VirtualAddress> {
        let vaddr = self.virtual_address_tracker.allocate(size)?;
        let range = MemoryRange {
            start: vaddr.into_inner(),
            end: vaddr.into_inner() + size,
        };
        self.back_and_map_range(range)
    }

    pub fn allocate_range(&mut self, mut range: MemoryRange) -> Option<VirtualAddress> {
        range.align_to_page();
        self.virtual_address_tracker.allocate_at_addr(range)?;
        self.back_and_map_range(range)
    }

    fn back_and_map_range(&self, range: MemoryRange) -> Option<VirtualAddress> {
        let virtual_mapper = VirtualMapper::new(self.frame_allocator);
        let num_frames = (range.end - range.start) / FRAME_SIZE;
        for idx in 0..num_frames {
            let backing_frame = self.frame_allocator.alloc_frame().expect("oom");
            let virt_mapping = VirtualMapping {
                cacheable: true,
                mutability: MemoryMutability::ReadWrite, // TODO
                phys: backing_frame.into_inner(),
                virt: range.start + (idx * FRAME_SIZE),
                size: FRAME_SIZE,
            };

            let pml4_phys = PhysicalAddress::new(PagingTable::current_pml4() as usize);
            let pml4_virt = pml4_phys.get_virt_addr::<PHYS_TO_VIRT_OFFSET>();
            virtual_mapper.map::<PHYS_TO_VIRT_OFFSET>(pml4_virt.as_ptr_mut(), &virt_mapping);
        }
        Some(VirtualAddress::new(range.start))
    }
}

#[derive(Clone, Copy, Debug)]
pub struct MemoryRange {
    start: usize,
    end: usize,
}

impl MemoryRange {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    fn size(&self) -> usize {
        self.end - self.start
    }

    fn contains_range(&self, other: Self) -> bool {
        other.start >= self.start && other.end <= self.end
    }

    fn consume_size(&mut self, size: usize) {
        assert!(self.size() >= size);
        self.start += size;
    }

    fn is_empty(&self) -> bool {
        self.size() == 0
    }

    fn align_to_page(&mut self) {
        let (start, end) =
            crate::memory::alloc::virtual_memory_mapper::page_bounds(self.start, self.end);
        self.start = start;
        self.end = end;
    }
}

struct VirtualAddressTracker<const PHYS_TO_VIRT_OFFSET: usize> {
    _frame_allocator: &'static PhysicalMemoryAllocator,
    node_pool: Pool,
    free_addr_ranges: LinkedList<MemoryRange>,
}

impl<const PHYS_TO_VIRT_OFFSET: usize> VirtualAddressTracker<PHYS_TO_VIRT_OFFSET> {
    fn new(frame_allocator: &'static PhysicalMemoryAllocator) -> Self {
        let backing_frame = frame_allocator.alloc_frame().expect("oom");
        let virt_addr_start = backing_frame.get_virt_addr::<PHYS_TO_VIRT_OFFSET>();
        let virt_addr_end = VirtualAddress::new(virt_addr_start.into_inner() + FRAME_SIZE - 1); // TODO is this minus 1 needed?

        let node_pool_sentinel_ptr_addr = VirtualAddress::new(
            virt_addr_end.into_inner() - core::mem::size_of::<MaybeUninit<LinkedListNode<Chunk>>>(),
        );
        let node_pool_sentinel_end_addr =
            VirtualAddress::new(node_pool_sentinel_ptr_addr.into_inner() - 1);
        let node_pool_sentinel_ptr: *mut MaybeUninit<LinkedListNode<Chunk>> =
            node_pool_sentinel_ptr_addr.as_ptr_mut();

        let free_ranges_sentinel_ptr_addr = VirtualAddress::new(
            node_pool_sentinel_end_addr.into_inner()
                - core::mem::size_of::<MaybeUninit<LinkedListNode<MemoryRange>>>(),
        );
        let free_ranges_sentinel_end_addr =
            VirtualAddress::new(free_ranges_sentinel_ptr_addr.into_inner() - 1);
        let free_ranges_sentinel_ptr: *mut MaybeUninit<LinkedListNode<MemoryRange>> =
            free_ranges_sentinel_ptr_addr.as_ptr_mut();

        let chunk_node_addr = VirtualAddress::new(
            free_ranges_sentinel_end_addr.into_inner()
                - core::mem::size_of::<LinkedListNode<Chunk>>(),
        );
        let chunk_end_addr = VirtualAddress::new(chunk_node_addr.into_inner() - 1);

        unsafe {
            *node_pool_sentinel_ptr = MaybeUninit::uninit();
        }
        unsafe {
            *free_ranges_sentinel_ptr = MaybeUninit::uninit();
        }

        unsafe {
            *chunk_node_addr.as_ptr_mut() =
                LinkedListNode::new(Chunk::new(virt_addr_start, chunk_end_addr));
        }

        let mut node_pool = unsafe { Pool::empty(node_pool_sentinel_ptr.as_mut().unwrap()) };
        unsafe { node_pool.add_chunk(chunk_node_addr.as_ptr_mut()) };

        let node = Self::mknode(
            &mut node_pool,
            MemoryRange {
                start: 0,
                end: usize::MAX,
            },
        );
        let mut ll = unsafe { LinkedList::new(free_ranges_sentinel_ptr.as_mut().unwrap()) };
        unsafe { ll.push_front(node) };

        Self {
            _frame_allocator: frame_allocator,
            node_pool,
            free_addr_ranges: ll,
        }
    }

    fn mknode(node_pool: &mut Pool, memory_range: MemoryRange) -> *mut LinkedListNode<MemoryRange> {
        let ptr = node_pool
            .try_alloc::<LinkedListNode<MemoryRange>>()
            .expect("failed to alloc");
        unsafe { *ptr = LinkedListNode::new(memory_range) };
        ptr
    }

    fn allocate(&mut self, size: usize) -> Option<VirtualAddress> {
        for mem_range_node in self.free_addr_ranges.iter_mut() {
            let mem_range = mem_range_node.data_mut();
            if mem_range.size() >= size {
                let start_addr = mem_range.start;
                mem_range.consume_size(size);
                if mem_range.is_empty() {
                    // mem_range_node.unlink_self();
                    todo!();
                }
                return Some(VirtualAddress::new(start_addr));
            }
        }
        None
    }

    fn allocate_at_addr(&mut self, desired_memory_range: MemoryRange) -> Option<VirtualAddress> {
        let mut free_range_cursor = self.free_addr_ranges.cursor();

        while let Some(free_range) = free_range_cursor.curr_data_mut() {
            if free_range.contains_range(desired_memory_range) {
                if desired_memory_range.start == free_range.start {
                    // if the desired range is at our start, all we need to
                    // do is consume the size as if we were just allocating
                    free_range.consume_size(desired_memory_range.size());
                    if free_range.is_empty() {
                        // free_range_node.unlink_self();
                        todo!();
                    }
                    return Some(VirtualAddress::new(desired_memory_range.start));
                } else {
                    // if the desired range is not at our start, we need to
                    // split the current range
                    let mut new_range =
                        MemoryRange::new(desired_memory_range.start, free_range.end);
                    free_range.end = desired_memory_range.start - 1;
                    new_range.consume_size(desired_memory_range.size());
                    if !free_range.is_empty() {
                        let node = Self::mknode(&mut self.node_pool, new_range);
                        unsafe { free_range_cursor.insert_after_curr(node) };
                    }
                    return Some(VirtualAddress::new(desired_memory_range.start));
                }
            }

            free_range_cursor.move_next();
        }
        None
    }
}

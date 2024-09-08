pub mod physical_memory_allocator;
pub mod userspace_allocator;
pub mod virtual_memory_allocator;
pub mod virtual_memory_mapper;

use core::mem::MaybeUninit;

use crate::collections::linked_list::{LinkedList, LinkedListNode};
pub use physical_memory_allocator::{PhysicalMemoryAllocator, FRAME_SIZE};
#[cfg(target_arch = "x86_64")]
pub use userspace_allocator::UserspaceAllocator;
#[cfg(target_arch = "x86_64")]
pub use virtual_memory_allocator::{MemoryRange, VirtualMemoryAllocator};

use crate::memory::VirtualAddress;

#[repr(C)]
#[derive(Copy, Clone, Debug)]
struct ChunkHeader {
    total_size: usize,
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum AllocationState {
    Free = 0,
    Used = 1,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
struct AllocationHeader {
    state: AllocationState,
    size: usize,
}

/// A Chunk of memory that may be completely used, completely unused, or some
/// in-between. The start and end of the overall memory is tracked as well as
/// the start of the free region.
pub struct Chunk {
    mem_start: VirtualAddress,
    mem_end: VirtualAddress,
}

impl Chunk {
    pub fn new(mem_start: VirtualAddress, mem_end: VirtualAddress) -> Self {
        let required_size =
            core::mem::size_of::<ChunkHeader>() + core::mem::size_of::<AllocationHeader>();
        let actual_size = mem_end.into_inner() - mem_start.into_inner();
        assert!(actual_size >= required_size);
        let chunk_header_ptr: *mut ChunkHeader = mem_start.as_ptr_mut();
        unsafe {
            *chunk_header_ptr = ChunkHeader {
                total_size: actual_size,
            };
        }
        let allocation_header_ptr: *mut AllocationHeader =
            VirtualAddress::new(mem_start.into_inner() + core::mem::size_of::<ChunkHeader>())
                .as_ptr_mut();
        unsafe {
            *allocation_header_ptr = AllocationHeader {
                state: AllocationState::Free,
                size: actual_size - core::mem::size_of::<ChunkHeader>(),
            };
        }
        Self { mem_start, mem_end }
    }

    /// Get the total size of the Chunk.
    pub fn size(&self) -> usize {
        self.mem_end.into_inner() - self.mem_start.into_inner()
    }

    pub fn contains(&self, ptr: *mut u8) -> bool {
        ((ptr as usize) > self.mem_start.into_inner())
            && ((ptr as usize) < self.mem_end.into_inner())
    }

    fn chunk_header(&self) -> ChunkHeader {
        let ptr: *const ChunkHeader = self.mem_start.as_ptr();
        unsafe { *ptr }
    }

    /// Attempt to allocate a pointer of type `T`. If unsuccessful, None is
    /// returned.
    pub fn try_alloc<T>(&mut self) -> Option<*mut T> {
        let layout = core::alloc::Layout::new::<T>();
        self.try_alloc_layout(layout)
            .map(|p| unsafe { core::mem::transmute(p) })
    }

    pub fn try_alloc_layout(&mut self, layout: core::alloc::Layout) -> Option<*mut u8> {
        // 1. We need to chase AllocationHeaders until we find one that is in
        // `state` Free, and then see if it has enough capacity to accomodate
        // `layout`.
        let chunk_header = self.chunk_header();
        let mut curr_addr =
            VirtualAddress::new(self.mem_start.into_inner() + core::mem::size_of::<ChunkHeader>());
        let end_addr = self.mem_start.into_inner() + chunk_header.total_size;
        loop {
            // we've gone through the whole Chunk and didn't find any
            // free slots
            if curr_addr.into_inner() >= end_addr {
                return None;
            }

            let allocation_header: *mut AllocationHeader = curr_addr.as_ptr_mut();
            let allocation_header = unsafe { &mut *allocation_header };
            // this slot is already used, keep going
            if allocation_header.state == AllocationState::Used {
                curr_addr = VirtualAddress::new(curr_addr.into_inner() + allocation_header.size);
                continue;
            }

            // 2. Determine whether we are naturally aligned
            let user_start = curr_addr.into_inner() + core::mem::size_of::<AllocationHeader>();
            let align_rem = user_start % layout.align();
            let start_addr = if align_rem == 0 {
                // naturally aligned, we can just mutate the existing header
                if user_start + layout.size() > curr_addr.into_inner() + allocation_header.size {
                    curr_addr =
                        VirtualAddress::new(curr_addr.into_inner() + allocation_header.size);
                    continue;
                }

                user_start
            } else {
                // if we're not naturally aligned, we're in a bit of a pickle.
                // in this case, we need to find the next address that is aligned
                // but this is a bit nuanced. we need to account for the current
                // AllocationHeader but since we scan forward, we'll also be introducing
                // a new bit of memory that will need to be tracked with another
                // AllocationHeader.
                //
                // for this reason we need to find the next address after `curr_addr`
                // that:
                // - is aligned to `layout.align()`
                // - is more than `size_of::<AllocationHeader>() * 2` bytes greater than
                //   `curr_addr
                let next_addr_not_counting_new_header = user_start + layout.align() - align_rem;
                let next_addr_counting_new_header = if next_addr_not_counting_new_header
                    - user_start
                    < core::mem::size_of::<AllocationHeader>()
                {
                    // the next aligned address is so close to the current address
                    // that there is no room for the new header. in this situation,
                    // we need to move forward by `layout.align()` so we can have enough space for
                    // a header
                    next_addr_not_counting_new_header + layout.align()
                } else {
                    // there was already enough of a gap to support a new AllocationHeader
                    // NB: this is probably not optimal. this can lead to degenerate
                    // situations where we have a bunch of AllocationHeaders describing
                    // arbitrarily small memory regions that could never realistically
                    // be used by an allocation. will probably need a real allocator
                    // algorithm instead of this hand-rolled jank
                    next_addr_not_counting_new_header
                };

                // at this point we'll need to create the new AllocationHeader if
                // and only if there's enough space to actually perform the allocation.
                if next_addr_counting_new_header + layout.size()
                    > curr_addr.into_inner() + allocation_header.size
                {
                    curr_addr =
                        VirtualAddress::new(curr_addr.into_inner() + allocation_header.size);
                    continue;
                }

                // we need to adjust the existing `allocation_header`'s size to
                // only go up to our new region.
                let end_addr = curr_addr.into_inner() + allocation_header.size;
                let new_allocation_header_addr =
                    next_addr_counting_new_header - core::mem::size_of::<AllocationHeader>();
                allocation_header.size = new_allocation_header_addr - curr_addr.into_inner();
                let new_allocation_header_ptr: *mut AllocationHeader =
                    VirtualAddress::new(new_allocation_header_addr).as_ptr_mut();
                unsafe {
                    *new_allocation_header_ptr = AllocationHeader {
                        state: AllocationState::Free,
                        size: end_addr - new_allocation_header_addr,
                    };
                }

                next_addr_counting_new_header
            };

            // 3. at this point, we have an address for the user data, we have
            // ensured that there's enough space at this address, and we have
            // potentially created new AllocationHeaders to accomodate any gaps
            // that will be introduced from alignment requirements. At this point
            // we need to actually perform the allocation, mark the Header as used,
            // and potentially create a new Header *after* the current header if
            // there is still remaining space in the Chunk.
            let alloction_header_addr =
                VirtualAddress::new(start_addr - core::mem::size_of::<AllocationHeader>());
            let alloction_header_ptr: *mut AllocationHeader = alloction_header_addr.as_ptr_mut();
            let allocation_header = unsafe { &mut *alloction_header_ptr };

            // this is a confusing condition because we subtract and add the same
            // size_of::<AllocationHeader>(). this is done because `size` includes
            // the current allocation header size, but we also want to see if theres
            // enough leftover memory that we can create a new header. in practice,
            // we could just use `allocation_header.size` but im including the subtraction
            // and addition to be explicit about the bookkeeping. this should be
            // refactored to be more intuitive about header bookkeeping
            if layout.size()
                < (allocation_header.size - core::mem::size_of::<AllocationHeader>())
                    + core::mem::size_of::<AllocationHeader>()
            {
                // we have enough leftover memory to introduce a new header after
                // our allocation
                let new_header_addr = start_addr + layout.size();
                let new_header_ptr = VirtualAddress::new(new_header_addr).as_ptr_mut();
                let new_header_size = allocation_header.size
                    - layout.size()
                    - core::mem::size_of::<AllocationHeader>();
                unsafe {
                    *new_header_ptr = AllocationHeader {
                        state: AllocationState::Free,
                        size: new_header_size,
                    }
                }
                allocation_header.size = layout.size() + core::mem::size_of::<AllocationHeader>();
            }
            allocation_header.state = AllocationState::Used;

            return Some(VirtualAddress::new(start_addr).as_ptr_mut());
        }
    }

    /// Free the memory for the given pointer. All this does is mark the region
    /// within the chunk as Free, there is no compaction or defragmentation.
    /// Allocation is responsible for compacting as it jumps from header to
    /// header if two contiguous headers are Free.
    ///
    /// # Safety
    /// `ptr` must be a pointer that was allocated with `self`
    pub unsafe fn dealloc(&mut self, ptr: *mut u8) {
        let allocation_header_addr = (ptr as usize) - core::mem::size_of::<AllocationHeader>();
        let allocation_header_ptr: *mut AllocationHeader = allocation_header_addr as _;
        let allocation_header = &mut *allocation_header_ptr;
        assert_eq!(
            allocation_header.state,
            AllocationState::Used,
            "trying to free an already freed pointer"
        );
        allocation_header.state = AllocationState::Free;
    }
}

#[cfg(all(test, not(feature = "no-std")))]
impl core::fmt::Debug for Chunk {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let chunk_header = self.chunk_header();
        f.write_fmt(format_args!("chunk header: {:?}\n", chunk_header))?;

        let mut curr_addr =
            VirtualAddress::new(self.mem_start.into_inner() + core::mem::size_of::<ChunkHeader>());
        let end_addr = self.mem_start.into_inner() + chunk_header.total_size;
        loop {
            if curr_addr.into_inner() >= end_addr {
                return Ok(());
            }
            let allocation_header: *const AllocationHeader = curr_addr.as_ptr();
            let allocation_header = unsafe { &*allocation_header };
            f.write_fmt(format_args!(
                "\tallocation_header: {:?}\n",
                allocation_header
            ))?;
            curr_addr = VirtualAddress::new(curr_addr.into_inner() + allocation_header.size);
        }
    }
}

/// A Pool represents a sequence of `Chunks` that can be allocated from.
///
/// Pools do not know how to allocate any new Physical or VirtualMemory outside
/// of the sequence of Chunks that its tracking. Instead, if an allocation
/// results in a Chunk splitting, the Chunk is returned and its up to the caller
/// to allocate a LinkedListNode with the Chunk. This allows a common memory
/// management implementation for divvying up already allocated chunks and
/// intends to break a cyclic dependency between the various memory management
/// layers, making Pools an abstraction used by both the top level HeapAllocator
/// as well as the lower level VirtualAddressAllocator.
pub struct Pool {
    chunks: LinkedList<Chunk>,
}

impl Pool {
    /// Create a new empty Pool.
    pub fn empty(bootstrapper: &mut MaybeUninit<LinkedListNode<Chunk>>) -> Self {
        Self {
            chunks: LinkedList::new(bootstrapper),
        }
    }

    /// Add a Chunk to the Pool
    ///
    /// # Safety
    /// `chunk` must be a pointer to a valid LinkedListNode<Chunk>
    pub unsafe fn add_chunk(&mut self, chunk: *mut LinkedListNode<Chunk>) {
        self.chunks.push_back(chunk);
    }

    /// Attempt to allocate a pointer of a given Layout. If unsuccessful, None
    /// is returned.
    pub fn try_alloc<T>(&mut self) -> Option<*mut T> {
        let layout = core::alloc::Layout::new::<T>();
        self.try_alloc_layout(layout)
            .map(|p| unsafe { core::mem::transmute(p) })
    }

    /// Attempt to allocate a pointer of a given Layout. If unsuccessful, None
    /// is returned.
    pub fn try_alloc_layout(&mut self, layout: core::alloc::Layout) -> Option<*mut u8> {
        for chunk_node in self.chunks.iter_mut() {
            let chunk = chunk_node.data_mut();
            if let Some(alloc_result) = chunk.try_alloc_layout(layout) {
                return Some(alloc_result);
            }
        }
        None
    }

    /// Deallocate the provided pointer
    ///
    /// # Safety
    ///
    /// The pointer must have been allocated with this instance of Pool.
    pub unsafe fn dealloc(&mut self, ptr: *mut u8) {
        for chunk_node in self.chunks.iter_mut() {
            let chunk = chunk_node.data_mut();
            if chunk.contains(ptr) {
                chunk.dealloc(ptr);
                return;
            }
        }

        panic!("failed to find `ptr` in managed chunks");
    }
}

// #[cfg(test)]
// mod pool_tests {
//     use super::*;
//
//     #[test]
//     fn alloc_on_empty_pool_returns_none() {
//         let mut bootstrapper = MaybeUninit::uninit();
//         let mut pool = Pool::empty(&mut bootstrapper);
//         let alloc_res = pool.try_alloc::<u32>();
//         assert!(alloc_res.is_none());
//     }
//
//     #[test]
//     fn can_add_new_chunks() {
//         let mut bootstrapper = MaybeUninit::uninit();
//         let mut pool = Pool::empty(&mut bootstrapper);
//
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//
//         let ll_node = Box::into_raw(Box::new(LinkedListNode::new(chunk)));
//         unsafe { pool.add_chunk(ll_node) };
//     }
//
//     #[test]
//     fn try_alloc_with_no_free_chunks_returns_none() {
//         let mut bootstrapper = MaybeUninit::uninit();
//         let mut pool = Pool::empty(&mut bootstrapper);
//
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let chunk = Chunk::new(
//             VirtualAddress::new(
//                 end - core::mem::size_of::<ChunkHeader>()
//                     - core::mem::size_of::<AllocationHeader>(),
//             ),
//             VirtualAddress::new(end),
//         );
//
//         let ll_node = Box::into_raw(Box::new(LinkedListNode::new(chunk)));
//         unsafe { pool.add_chunk(ll_node) };
//         let alloc_res = pool.try_alloc::<u32>();
//         assert!(alloc_res.is_none());
//     }
//
//     #[test]
//     fn try_alloc_with_free_chunk_returns_some() {
//         let mut bootstrapper = MaybeUninit::uninit();
//         let mut pool = Pool::empty(&mut bootstrapper);
//
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//
//         let ll_node = Box::into_raw(Box::new(LinkedListNode::new(chunk)));
//         unsafe { pool.add_chunk(ll_node) };
//         let alloc_res = pool.try_alloc::<u32>();
//         alloc_res.expect("failed to allocate");
//     }
//
//     #[test]
//     fn try_alloc_checks_all_chunks() {
//         let mut bootstrapper = MaybeUninit::uninit();
//         let mut pool = Pool::empty(&mut bootstrapper);
//
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let chunk = Chunk::new(
//             VirtualAddress::new(
//                 end - core::mem::size_of::<ChunkHeader>()
//                     - core::mem::size_of::<AllocationHeader>(),
//             ),
//             VirtualAddress::new(end),
//         );
//
//         let ll_node = Box::into_raw(Box::new(LinkedListNode::new(chunk)));
//         unsafe { pool.add_chunk(ll_node) };
//
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//
//         let ll_node = Box::into_raw(Box::new(LinkedListNode::new(chunk)));
//         unsafe { pool.add_chunk(ll_node) };
//
//         let alloc_res = pool.try_alloc::<u32>();
//         alloc_res.expect("failed to allocate");
//     }
// }
//
// #[cfg(test)]
// #[ignore]
// mod chunk_tests {
//     use super::*;
//
//     #[test]
//     fn chunk_creation_works_with_minimum_space_needed() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let minimum_space_needed =
//             core::mem::size_of::<ChunkHeader>() + core::mem::size_of::<AllocationHeader>();
//         Chunk::new(
//             VirtualAddress::new(end - minimum_space_needed),
//             VirtualAddress::new(end),
//         );
//     }
//
//     #[test]
//     #[should_panic]
//     fn chunk_creation_panics_if_not_enough_size_for_metadata() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let minimum_space_needed =
//             core::mem::size_of::<ChunkHeader>() + core::mem::size_of::<AllocationHeader>();
//         Chunk::new(
//             VirtualAddress::new(end - minimum_space_needed + 1),
//             VirtualAddress::new(end),
//         );
//     }
//
//     #[test]
//     fn chunk_creation_creates_chunk_header() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         let chunk_header: *const ChunkHeader = start as _;
//         let chunk_header = unsafe { &*chunk_header };
//         assert_eq!(chunk_header.total_size, end - start);
//     }
//
//     #[test]
//     fn chunk_creation_creates_initial_allocation_header() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         let allocation_header: *const AllocationHeader =
//             (start + core::mem::size_of::<ChunkHeader>()) as _;
//         let allocation_header = unsafe { &*allocation_header };
//         assert_eq!(allocation_header.state, AllocationState::Free);
//         assert_eq!(
//             allocation_header.size,
//             end - start - core::mem::size_of::<ChunkHeader>()
//         );
//     }
//
//     #[test]
//     fn chunk_size_returns_total_size_of_chunk() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         assert_eq!(chunk.size(), end - start);
//     }
//
//     #[test]
//     fn alloc_on_full_chunk_returns_none() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let mut chunk = Chunk::new(
//             VirtualAddress::new(
//                 end - core::mem::size_of::<ChunkHeader>()
//                     - core::mem::size_of::<AllocationHeader>(),
//             ),
//             VirtualAddress::new(end),
//         );
//         let maybe_ptr = chunk.try_alloc::<u32>();
//         assert!(maybe_ptr.is_none());
//     }
//
//     #[test]
//     fn alloc_on_empty_chunk_returns_some() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let mut chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         let maybe_ptr = chunk.try_alloc::<u32>();
//         let ptr = maybe_ptr.expect("failed to alloc");
//         assert_eq!(
//             ptr as usize,
//             start + core::mem::size_of::<ChunkHeader>() + core::mem::size_of::<AllocationHeader>()
//         );
//     }
//
//     #[test]
//     fn successful_allocation_mutates_allocation_headers_correctly() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let mut chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         let ptr = chunk.try_alloc::<u32>().expect("failed to alloc");
//
//         // validate our pointer is where we expect
//         assert_eq!(
//             ptr as usize,
//             start + core::mem::size_of::<ChunkHeader>() + core::mem::size_of::<AllocationHeader>()
//         );
//
//         // validate that the allocation header was mutated to be used and shrunk
//         // to size of allocation
//         let allocation_header_ptr: *const AllocationHeader =
//             ((ptr as usize) - core::mem::size_of::<AllocationHeader>()) as _;
//         let allocation_header = unsafe { *allocation_header_ptr };
//         assert_eq!(allocation_header.state, AllocationState::Used);
//         assert_eq!(
//             allocation_header.size,
//             core::mem::size_of::<u32>() + core::mem::size_of::<AllocationHeader>()
//         );
//
//         // validate that a new allocation header was created after our allocation
//         let allocation_header_ptr: *const AllocationHeader =
//             (allocation_header_ptr as usize + allocation_header.size) as _;
//         let allocation_header = unsafe { *allocation_header_ptr };
//         assert_eq!(allocation_header.state, AllocationState::Free);
//         assert_eq!(
//             allocation_header.size,
//             end - start
//                 - core::mem::size_of::<ChunkHeader>()
//                 - core::mem::size_of::<u32>()
//                 - core::mem::size_of::<AllocationHeader>()
//         );
//     }
//
//     #[test]
//     fn successive_allocs_on_empty_chunk_returns_new_ptrs() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let mut chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         for i in 0..10 {
//             let maybe_ptr = chunk.try_alloc::<u32>();
//             let ptr = maybe_ptr.expect("failed to alloc");
//             assert_eq!(
//                 ptr as usize,
//                 (start
//                     + core::mem::size_of::<ChunkHeader>()
//                     + ((i + 1) * core::mem::size_of::<AllocationHeader>())
//                     + (i * core::mem::size_of::<u32>())),
//                 "iter: {}",
//                 i
//             );
//         }
//     }
//
//     #[test]
//     fn alloc_on_unaligned_boundary_creates_new_allocation_slot() {
//         #[repr(C, align(32))]
//         struct MyType {
//             i: u128,
//         }
//         let my_align = core::alloc::Layout::new::<MyType>().align();
//         assert_eq!(my_align, 32);
//
//         let buf: [u8; 4096] = [0; 4096];
//         let buf_start = core::ptr::addr_of!(buf) as usize;
//         let buf_end = buf_start + 4095;
//         let user_start = buf_start
//             + core::mem::size_of::<ChunkHeader>()
//             + core::mem::size_of::<AllocationHeader>();
//         let chunk_start = if user_start % my_align == 0 {
//             buf_start + 4
//         } else {
//             buf_start
//         };
//         let mut chunk = Chunk::new(
//             VirtualAddress::new(chunk_start),
//             VirtualAddress::new(buf_end),
//         );
//         // we're allocating something with an 32-byte alignment on a 4-byte boundary
//         // because the chunk starts at address 4. the Chunk should leave a gap
//         // since it needs to skip ahead in order to satisfy the alignment
//         let maybe_ptr = chunk.try_alloc::<MyType>();
//         let ptr = maybe_ptr.expect("failed to alloc");
//
//         let expected_allocation_location = chunk_start
//             + core::mem::size_of::<ChunkHeader>()
//             + core::mem::size_of::<AllocationHeader>()
//             + (user_start % my_align)
//             + core::mem::size_of::<AllocationHeader>();
//         assert_eq!(ptr as usize, expected_allocation_location);
//
//         let expected_gap_header_addr = chunk_start + core::mem::size_of::<ChunkHeader>();
//         let expected_gap_header_ptr: *const AllocationHeader = expected_gap_header_addr as _;
//         let expected_gap_header = unsafe { &*expected_gap_header_ptr };
//         assert_eq!(expected_gap_header.state, AllocationState::Free);
//         assert_eq!(
//             expected_gap_header.size,
//             core::mem::size_of::<AllocationHeader>() + (user_start % my_align)
//         );
//
//         let expected_used_header_addr = expected_gap_header_addr + expected_gap_header.size;
//         let expected_used_header_ptr: *const AllocationHeader = expected_used_header_addr as _;
//         let expected_used_header = unsafe { &*expected_used_header_ptr };
//         assert_eq!(expected_used_header.state, AllocationState::Used);
//         assert_eq!(
//             expected_used_header.size,
//             core::mem::size_of::<MyType>() + core::mem::size_of::<AllocationHeader>()
//         );
//
//         let expected_tail_header_addr = expected_used_header_addr + expected_used_header.size;
//         let expected_tail_header_ptr: *const AllocationHeader = expected_tail_header_addr as _;
//         let expected_tail_header = unsafe { &*expected_tail_header_ptr };
//         assert_eq!(expected_tail_header.state, AllocationState::Free);
//         assert_eq!(
//             expected_tail_header.size,
//             buf_end
//                 - buf_start
//                 - core::mem::size_of::<ChunkHeader>()
//                 - expected_gap_header.size
//                 - expected_used_header.size
//         );
//     }
//
//     #[test]
//     #[ignore]
//     fn alloc_on_unaligned_boundary_handles_gap_smaller_than_allocation_header() {
//         todo!()
//     }
//
//     #[test]
//     fn dealloc_marks_region_as_free() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let mut chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         let ptr = chunk.try_alloc::<u32>().expect("failed to alloc");
//
//         // validate our pointer is where we expect
//         assert_eq!(
//             ptr as usize,
//             start + core::mem::size_of::<ChunkHeader>() + core::mem::size_of::<AllocationHeader>()
//         );
//
//         // validate that the allocation header was mutated to be used and shrunk
//         // to size of allocation
//         let allocation_header_ptr: *const AllocationHeader =
//             ((ptr as usize) - core::mem::size_of::<AllocationHeader>()) as _;
//         let allocation_header = unsafe { *allocation_header_ptr };
//         assert_eq!(allocation_header.state, AllocationState::Used);
//         assert_eq!(
//             allocation_header.size,
//             core::mem::size_of::<u32>() + core::mem::size_of::<AllocationHeader>()
//         );
//
//         unsafe { chunk.dealloc(ptr as _) };
//
//         // validate the allocaiton head now says Free
//         let allocation_header_ptr: *const AllocationHeader =
//             ((ptr as usize) - core::mem::size_of::<AllocationHeader>()) as _;
//         let allocation_header = unsafe { *allocation_header_ptr };
//         assert_eq!(allocation_header.state, AllocationState::Free);
//         assert_eq!(
//             allocation_header.size,
//             core::mem::size_of::<u32>() + core::mem::size_of::<AllocationHeader>()
//         );
//     }
//
//     #[test]
//     #[should_panic]
//     fn dealloc_panics_on_double_free() {
//         let buf: [u8; 4096] = [0; 4096];
//         let start = core::ptr::addr_of!(buf) as usize;
//         let end = start + 4095;
//         let mut chunk = Chunk::new(VirtualAddress::new(start), VirtualAddress::new(end));
//         let ptr = chunk.try_alloc::<u32>().expect("failed to alloc");
//
//         // validate our pointer is where we expect
//         assert_eq!(
//             ptr as usize,
//             start + core::mem::size_of::<ChunkHeader>() + core::mem::size_of::<AllocationHeader>()
//         );
//
//         // validate that the allocation header was mutated to be used and shrunk
//         // to size of allocation
//         let allocation_header_ptr: *const AllocationHeader =
//             ((ptr as usize) - core::mem::size_of::<AllocationHeader>()) as _;
//         let allocation_header = unsafe { *allocation_header_ptr };
//         assert_eq!(allocation_header.state, AllocationState::Used);
//         assert_eq!(
//             allocation_header.size,
//             core::mem::size_of::<u32>() + core::mem::size_of::<AllocationHeader>()
//         );
//
//         unsafe { chunk.dealloc(ptr as _) };
//         unsafe { chunk.dealloc(ptr as _) };
//     }
// }

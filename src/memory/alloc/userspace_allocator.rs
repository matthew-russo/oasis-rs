#![cfg(target_arch = "x86_64")]

use crate::collections::linked_list::LinkedListNode;
use crate::memory::alloc::{Chunk, MemoryRange, Pool, VirtualMemoryAllocator};
use crate::memory::VirtualAddress;
use crate::sync::spinlock::Spinlock;

use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicUsize, Ordering};

// UserspaceAllocator only operates on the VirtualAddress space, divying up chunks
// of already-physically-allocated-and-mapped memory for objects. The
// UserspaceAllocator manages this memory though a linked-list of arbitrarilly sized
// chunks that may be free or in-use.
pub struct UserspaceAllocator<const PHYS_TO_VIRT_OFFSET: usize, const HEAP_START: usize> {
    heap_current: AtomicUsize,
    virtual_address_allocator: Spinlock<Option<VirtualMemoryAllocator<PHYS_TO_VIRT_OFFSET>>>,
    pool: Spinlock<Option<Pool>>,
}

impl<const PHYS_TO_VIRT_OFFSET: usize, const HEAP_START: usize>
    UserspaceAllocator<PHYS_TO_VIRT_OFFSET, HEAP_START>
{
    // This was very arbitrary...
    const ALLOC_SIZE: usize = 4096 * 8; // Allocate 8 pages at a time

    pub const fn uninit() -> Self {
        Self {
            heap_current: AtomicUsize::new(HEAP_START),
            virtual_address_allocator: Spinlock::new(None),
            pool: Spinlock::new(None),
        }
    }

    pub fn initialize(
        &self,
        virtual_address_allocator: VirtualMemoryAllocator<PHYS_TO_VIRT_OFFSET>,
        pool_sentinel: &mut MaybeUninit<LinkedListNode<Chunk>>,
    ) {
        let mut alloc = self.virtual_address_allocator.lock();
        *alloc = Some(virtual_address_allocator);

        let mut pool = self.pool.lock();
        *pool = Some(Pool::empty(pool_sentinel));
    }

    pub fn alloc_bytes<const NUM_BYTES: usize>(&self) -> *mut u8 {
        self.alloc_ty::<[u8; NUM_BYTES]>() as *mut u8
    }

    pub fn alloc_ty<T>(&self) -> *mut T {
        let layout = core::alloc::Layout::new::<T>();
        self.alloc_layout(layout) as *mut T
    }

    fn alloc_layout(&self, layout: core::alloc::Layout) -> *mut u8 {
        let mut pool = self.pool.lock();
        let pool = pool.as_mut().unwrap();

        match pool.try_alloc_layout(layout) {
            Some(ptr) => ptr,
            None => {
                let mut virtual_address_allocator = self.virtual_address_allocator.lock();
                let heap_current = self
                    .heap_current
                    .fetch_add(Self::ALLOC_SIZE, Ordering::Relaxed);
                let start_addr = virtual_address_allocator
                    .as_mut()
                    .unwrap()
                    .allocate_range(MemoryRange::new(
                        heap_current,
                        heap_current + Self::ALLOC_SIZE,
                    ))
                    .expect("oom");
                let mut chunk = Chunk::new(
                    start_addr,
                    VirtualAddress::new(start_addr.into_inner() + Self::ALLOC_SIZE),
                );
                // using this very chunk, we'll allocate a LinkedListNode for it so we can track
                // it in the pool
                let ptr = chunk.try_alloc::<LinkedListNode<Chunk>>().expect("oom");
                unsafe {
                    *ptr = LinkedListNode::new(chunk);
                    pool.add_chunk(ptr);
                }
                pool.try_alloc_layout(layout).expect("oom")
            }
        }
    }

    unsafe fn dealloc_ptr(&self, ptr: *mut u8) {
        let mut pool = self.pool.lock();
        let pool = pool.as_mut().unwrap();
        pool.dealloc(ptr);
    }
}

unsafe impl<const PHYS_TO_VIRT_OFFSET: usize, const HEAP_START: usize> core::alloc::GlobalAlloc
    for UserspaceAllocator<PHYS_TO_VIRT_OFFSET, HEAP_START>
{
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        self.alloc_layout(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: core::alloc::Layout) {
        self.dealloc_ptr(ptr);
    }
}

unsafe impl<const PHYS_TO_VIRT_OFFSET: usize, const HEAP_START: usize> Send
    for UserspaceAllocator<PHYS_TO_VIRT_OFFSET, HEAP_START>
{
}

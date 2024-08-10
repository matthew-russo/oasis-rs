use crate::collections::linked_list::{LinkedList, LinkedListNode};
use crate::memory::{MemoryDefinition, PhysicalAddress};
use crate::sync::spinlock::Spinlock;

use core::mem::MaybeUninit;

pub const FRAME_SIZE: usize = 4096;

#[derive(Debug)]
pub struct Frame {
    mem_start: PhysicalAddress,
}

// TODO These shouldn't be behind a Spinlock, can probably move to using the
// AtomicLinkedList once we fix a couple more bugs
pub struct PhysicalMemoryManager {
    free: Spinlock<LinkedList<Frame>>,
    used: Spinlock<LinkedList<Frame>>,
    pub internally_used_memory: (PhysicalAddress, PhysicalAddress),
}

impl PhysicalMemoryManager {
    /// # Safety
    /// `mem_map` must be a valid MemoryMap
    pub unsafe fn new<M: MemoryDefinition>(mem: &M) -> Self {
        let num_frame_nodes_per_frame = FRAME_SIZE / core::mem::size_of::<LinkedListNode<Frame>>();
        let mut frame_iter = mem.free_frames(FRAME_SIZE);

        // NB: this leaks most of a frame and is being done out of laziness. i
        // expect to rework most of these memory allocators and the underlying
        // data structures so i'm not too concerned about optimizing around their
        // poor ergonomics
        let sentinel_backing_frame = frame_iter.next_back().expect("no frames in back");
        let end_of_internally_used_mem =
            PhysicalAddress::new(sentinel_backing_frame.into_inner() + FRAME_SIZE);

        let free_sentinel =
            sentinel_backing_frame.into_inner() as *mut MaybeUninit<LinkedListNode<Frame>>;
        *free_sentinel = MaybeUninit::uninit();
        let used_sentinel = (sentinel_backing_frame.into_inner()
            + core::mem::size_of::<MaybeUninit<LinkedListNode<Frame>>>())
            as *mut MaybeUninit<LinkedListNode<Frame>>;
        *used_sentinel = MaybeUninit::uninit();

        let mut free = LinkedList::new(free_sentinel.as_mut().unwrap());
        let used = LinkedList::new(used_sentinel.as_mut().unwrap());

        let mut curr_backing_frame = frame_iter.next_back().expect("no frames in back");
        let mut frame_count_for_curr_backing_frame = 0;

        while let Some(frame_mem_start) = frame_iter.next() {
            let frame_ptr = (curr_backing_frame.into_inner()
                + (frame_count_for_curr_backing_frame
                    * core::mem::size_of::<LinkedListNode<Frame>>()))
                as *mut LinkedListNode<Frame>;
            *frame_ptr = LinkedListNode::new(Frame {
                mem_start: frame_mem_start,
            });

            free.push_back(frame_ptr);
            frame_count_for_curr_backing_frame += 1;
            // TODO this approach is wasteful as we don't use the remainder of the frame if
            // two frames are contiguous
            if frame_count_for_curr_backing_frame >= num_frame_nodes_per_frame {
                curr_backing_frame = match frame_iter.next_back() {
                    Some(cbf) => cbf,
                    None => panic!("no frames in back"),
                };
                frame_count_for_curr_backing_frame = 0;
            }
        }

        let start_of_internally_used_mem = curr_backing_frame;

        Self {
            free: Spinlock::new(free),
            used: Spinlock::new(used),
            internally_used_memory: (start_of_internally_used_mem, end_of_internally_used_mem),
        }
    }

    /// Allocate a single frame of `FRAME_SIZE`.
    ///
    /// Returns None if there are no free frames
    pub fn alloc_frame(&self) -> Option<PhysicalAddress> {
        let mut free = self.free.lock();
        let mut used = self.used.lock();
        unsafe {
            let frame_node = free.pop_front()?;
            let addr = (*frame_node).data().mem_start;
            used.push_back(frame_node);
            Some(addr)
        }
    }

    /// Allocates a contiguous range of `size` bytes. Optionally
    /// allows specification of the alignment of the allocation.
    ///
    /// Assumes that `self.free` is ordered
    ///
    /// Returns None if there is no contiguous sequence of frames
    /// with the given alignment.
    pub fn alloc_contiguous(
        &self,
        size: usize,
        alignment: Option<usize>,
    ) -> Option<PhysicalAddress> {
        let num_frames_needed = if size % FRAME_SIZE == 0 {
            size / FRAME_SIZE
        } else {
            (size / FRAME_SIZE) + 1
        };

        let mut free = self.free.lock();
        let mut used = self.used.lock();
        unsafe {
            if (free.len()) < num_frames_needed {
                return None;
            }

            // 1. Find if there is a subsequence of contiguous frames large enough for
            // `size`, with the given alignment
            let mut start_mem = None;
            let mut prev_mem = PhysicalAddress::new(0);
            let mut found_start = None;
            for ll_node in free.iter() {
                let current_mem = ll_node.data().mem_start;
                let _local_prev_mem = prev_mem;

                if start_mem.is_none() {
                    start_mem = Some(current_mem);
                }

                // if this new frame isn't contiguous with our last frame, reset
                // our start
                if current_mem.into_inner() != prev_mem.into_inner() + FRAME_SIZE {
                    start_mem = Some(current_mem);
                }
                prev_mem = current_mem;

                // check alignment
                if let (Some(sm), Some(alignment)) = (start_mem, alignment) {
                    if sm.into_inner() % alignment != 0 {
                        start_mem = None;
                        continue;
                    }
                }

                if current_mem.into_inner() + FRAME_SIZE - start_mem.unwrap().into_inner()
                    >= size
                {
                    // WE FOUND IT
                    found_start = Some(start_mem.unwrap());
                    break;
                }
            }

            // 2. If we found a memory start, we now need to remove that subsection
            // of the free list. To do this we pop off the list in to our placeholder
            // list until we find the start node.
            let found_start = match found_start {
                Some(found_start) => found_start,
                None => return None,
            };

            let mut sentinel = MaybeUninit::uninit();

            let mut temp_free_first_half = LinkedList::new(&mut sentinel);
            while let Some(llnode) = free.pop_front() {
                let llnode_ref = &*llnode;
                if llnode_ref.data().mem_start == found_start {
                    free.push_front(llnode);
                    break;
                }
                temp_free_first_half.push_back(llnode);
            }

            // 3. The first node in `free` is now the the start node of the
            // memory range we are allocating. We now need to pop `num_frames_needed`
            // frames off of `free`, push them on to the back of `used`.
            for _ in 0..num_frames_needed {
                let llnode = free.pop_front().unwrap();
                used.push_back(llnode);
            }

            // 4. Lastly we need to reconnect our temporary list and `free`
            // NB: theres nothing to do with the sentinel_ptr we get back because
            // its stack allocated above. we can validate that by asserting the
            // addreses match
            let sentinel_ptr = free.prepend(temp_free_first_half);
            assert_eq!(sentinel_ptr, sentinel.as_mut_ptr());

            Some(found_start)
        }
    }

    pub fn dealloc_frame(&self, addr: PhysicalAddress) {
        let mut free = self.free.lock();
        let mut used = self.used.lock();

        let mut used_cursor = used.cursor();
        used_cursor.move_next();
        while let Some(used_frame_data) = used_cursor.curr_data() {
            if used_frame_data.mem_start == addr {
                let freed_frame = used_cursor
                    .remove_curr()
                    .expect("already validated that current is some");

                let mut free_cursor = free.cursor();
                free_cursor.move_next();
                while let Some(free_frame_data) = free_cursor.curr_data() {
                    if free_frame_data.mem_start.into_inner() > addr.into_inner() {
                        unsafe {
                            free_cursor.insert_before_curr(freed_frame);
                        }
                        return;
                    }
                    free_cursor.move_next();
                }

                unsafe { free.push_back(freed_frame) };

                return;
            }

            used_cursor.move_next();
        }
        panic!("failed to find frame in used list: {:?}", addr);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::memory::test_utils::BufferMemory;

    #[test]
    fn can_construct_physical_memory_manager() {
        let buf_mem = BufferMemory::<{ FRAME_SIZE * 32 }>::new();
        unsafe { PhysicalMemoryManager::new(&buf_mem) };
    }

    #[test]
    fn can_alloc_frame() {
        let buf_mem = BufferMemory::<{ FRAME_SIZE * 32 }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };
        let frame = frame_alloc.alloc_frame().expect("failed to allocate");
        assert_eq!(
            frame.into_inner(),
            core::ptr::addr_of!(*buf_mem.buffer()) as *const u8 as usize,
        );
    }

    #[test]
    fn can_alloc_multiple_frames() {
        const NUM_FRAMES: usize = 32;
        let buf_mem = BufferMemory::<{ FRAME_SIZE * NUM_FRAMES }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };

        for frame_num in 0..(NUM_FRAMES / 2) {
            let frame = frame_alloc
                .alloc_frame()
                .unwrap_or_else(|| panic!("failed to allocate at frame_num: {}", frame_num));
            let buf_addr = core::ptr::addr_of!(*buf_mem.buffer()) as *const u8 as usize;
            let expected_addr = buf_addr + (frame_num * FRAME_SIZE);
            assert_eq!(frame.into_inner(), expected_addr);
        }
    }

    #[test]
    fn can_alloc_contiguous_no_alignment() {
        const NUM_FRAMES: usize = 32;
        let buf_mem = BufferMemory::<{ FRAME_SIZE * NUM_FRAMES }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };

        let frame = frame_alloc
            .alloc_contiguous(FRAME_SIZE * 4, None)
            .expect("failed to allocate");
        assert_eq!(
            frame.into_inner(),
            core::ptr::addr_of!(*buf_mem.buffer()) as *const u8 as usize,
        );
    }

    #[test]
    fn can_alloc_contiguous_with_alignment() {
        const NUM_FRAMES: usize = 32;
        let buf_mem = BufferMemory::<{ FRAME_SIZE * NUM_FRAMES }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };

        let buf_addr = core::ptr::addr_of!(*buf_mem.buffer()) as *const u8 as usize;

        let mut alignment = 0;
        for i in 0..32 {
            if buf_addr % (FRAME_SIZE * (i + 1)) != 0 {
                alignment = i;
            }
        }
        assert_ne!(alignment, 0);

        // allocate 4 frames, with an alignment that will force
        // the frame allocator to not use the beginning of the buffer.
        let frame = frame_alloc
            .alloc_contiguous(FRAME_SIZE * 2, Some(alignment))
            .expect("failed to allocate");

        assert_ne!(frame.into_inner(), buf_addr);
    }

    #[test]
    #[should_panic]
    fn deallocing_wrong_frame_panics() {
        let buf_mem = BufferMemory::<{ FRAME_SIZE * 32 }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };
        frame_alloc.dealloc_frame(PhysicalAddress::new(0));
    }

    #[test]
    fn can_dealloc_frame() {
        let buf_mem = BufferMemory::<{ FRAME_SIZE * 32 }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };
        let frame = frame_alloc.alloc_frame().expect("failed to allocate");
        frame_alloc.dealloc_frame(frame);
    }

    #[test]
    fn dealloc_frame_removes_frame_from_used() {
        let buf_mem = BufferMemory::<{ FRAME_SIZE * 32 }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };
        let frame = frame_alloc.alloc_frame().expect("failed to allocate");
        frame_alloc.dealloc_frame(frame);
        let used = frame_alloc.used.lock();
        assert!(used.is_empty());
    }

    #[test]
    fn dealloc_frame_inserts_frame_into_free() {
        let buf_mem = BufferMemory::<{ FRAME_SIZE * 32 }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };
        let total_free = {
            let free = frame_alloc.free.lock();
            free.len()
        };
        let frame = frame_alloc.alloc_frame().expect("failed to allocate");
        let free_after_alloc = {
            let free = frame_alloc.free.lock();
            free.len()
        };
        assert_ne!(total_free, free_after_alloc);
        frame_alloc.dealloc_frame(frame);
        let free = frame_alloc.free.lock();
        for free_frame in free.iter() {
            if free_frame.data().mem_start == frame {
                return;
            }
        }
        panic!("didn't find dealloc'ed frame in free list");
    }

    #[test]
    fn dealloc_frame_inserts_frame_into_free_in_order() {
        let buf_mem = BufferMemory::<{ FRAME_SIZE * 32 }>::new();
        let frame_alloc = unsafe { PhysicalMemoryManager::new(&buf_mem) };

        let (expected_first_frame, expected_second_frame) = unsafe {
            let free = frame_alloc.free.lock();
            let first = free.head().unwrap();
            let second = (*first).peek_next_data().unwrap();
            ((*first).data().mem_start, second.mem_start)
        };

        let first_frame = frame_alloc.alloc_frame().expect("failed to allocate");
        let second_frame = frame_alloc.alloc_frame().expect("failed to allocate");

        assert_eq!(first_frame, expected_first_frame);
        assert_eq!(second_frame, expected_second_frame);

        // dealloc first_frame first. we expect this to be inserted at
        // the head
        frame_alloc.dealloc_frame(first_frame);
        unsafe {
            let free = frame_alloc.free.lock();
            let first_after_dealloc = free.head().unwrap();
            assert_eq!((*first_after_dealloc).data().mem_start, first_frame);
        }

        // since we dealloced the first frame first, this created a gap in the free list
        // that the second frame should fill
        frame_alloc.dealloc_frame(second_frame);
        unsafe {
            let free = frame_alloc.free.lock();
            let first_after_dealloc = free.head().unwrap();
            assert_eq!((*first_after_dealloc).data().mem_start, first_frame);
            let second_after_dealloc = (*first_after_dealloc).peek_next_data().unwrap();
            assert_eq!((*second_after_dealloc).mem_start, second_frame);
        }
    }
}

use super::{MemoryDefinition, PhysicalAddress};

/// MemoryMap describes memory ranges that are available to use.
///
/// internally structured as a C-style array of MemoryMapEntries, but
/// provides a more ergonomic interface through an implementation of
/// `MemoryDefinition`
#[derive(Debug)]
#[repr(C)]
pub struct MemoryMap {
    /// a C-style array of MemoryMapEntries, this pointing to the first entry
    data: *mut MemoryMapEntry,
    /// the number of entries in the `data` array
    num_entries: usize,
    /// the total amount of memory consumed by the `data` array
    mem_size: usize,
}

impl MemoryMap {
    /// construct a new MemoryMap
    ///
    /// # Safety
    ///
    /// `data` must be a pointer to a valid C-style array of MemoryMapEntry's
    pub unsafe fn new(data: *mut MemoryMapEntry, mem_size: usize, num_entries: usize) -> Self {
        Self {
            data,
            mem_size,
            num_entries,
        }
    }

    /// get the memory size
    pub fn mem_size(&self) -> usize {
        self.mem_size
    }

    /// get the memory size
    pub fn num_entries(&self) -> usize {
        self.num_entries
    }

    /// access the MemoryMapEntry's as an immutable slice
    pub fn as_slice(&self) -> &[MemoryMapEntry] {
        unsafe { core::slice::from_raw_parts(self.data, self.num_entries) }
    }

    /// access the MemoryMapEntry's as a mutable slice
    pub fn as_mut_slice(&mut self) -> &mut [MemoryMapEntry] {
        unsafe { core::slice::from_raw_parts_mut(self.data, self.num_entries) }
    }
}

impl MemoryDefinition for MemoryMap {
    type FreeFrameIter<'a> = FreeFrameIter<'a> where Self: 'a;

    fn free_frames(&self, frame_size: usize) -> Self::FreeFrameIter<'_> {
        FreeFrameIter::new(self.as_slice(), frame_size)
    }
}

pub struct FreeFrameIter<'a> {
    entry_slice: &'a [MemoryMapEntry],
    frame_size: usize,

    front_entry: Option<usize>,
    curr_location_in_front_entry: usize,

    back_entry: Option<usize>,
    curr_location_in_back_entry: usize,
}

impl<'a> FreeFrameIter<'a> {
    fn new(entry_slice: &'a [MemoryMapEntry], frame_size: usize) -> Self {
        FreeFrameIter {
            entry_slice,
            frame_size,

            front_entry: Some(0),
            curr_location_in_front_entry: entry_slice
                .first()
                .map(|e| e.free_start)
                .unwrap_or_default(),

            back_entry: Some(entry_slice.len().saturating_sub(1)),
            curr_location_in_back_entry: entry_slice
                .get(entry_slice.len().saturating_sub(1))
                .map(|e| e.phys_end - frame_size)
                .unwrap_or_default(),
        }
    }

    fn validate_front_and_back_havent_crossed(&self) -> Option<()> {
        use core::cmp::Ordering;
        match self.front_entry.cmp(&self.back_entry) {
            // front ptr before back ptr, good to still iterate
            Ordering::Less => Some(()),
            Ordering::Equal => {
                match self
                    .curr_location_in_front_entry
                    .cmp(&self.curr_location_in_back_entry)
                {
                    Ordering::Less => Some(()),
                    // if we're at the same location, this is the last valid iteration and next
                    // call to `next` or `next_back` will take a different branch
                    Ordering::Equal => Some(()),
                    Ordering::Greater => None,
                }
            }
            // front ptr after back ptr, iter exhausted
            Ordering::Greater => None,
        }
    }

    fn move_forward_one_entry(&mut self) {
        match self.front_entry.take() {
            Some(usize::MAX) => self.front_entry = None,
            Some(n) => {
                let new_front_entry = n + 1;
                self.curr_location_in_front_entry = self
                    .entry_slice
                    .get(new_front_entry)
                    .map(|e| e.free_start)
                    .unwrap_or_default();
                self.front_entry = Some(new_front_entry);
            }
            None => (),
        }
    }

    fn move_backward_one_entry(&mut self) {
        match self.back_entry.take() {
            Some(0) => self.back_entry = None,
            Some(n) => {
                let new_back_entry = n - 1;
                self.curr_location_in_back_entry = self
                    .entry_slice
                    .get(new_back_entry)
                    .map(|e| e.phys_end - self.frame_size)
                    .unwrap_or_default();
                self.back_entry = Some(new_back_entry);
            }
            None => (),
        }
    }
}

impl Iterator for FreeFrameIter<'_> {
    type Item = PhysicalAddress;

    fn next(&mut self) -> Option<Self::Item> {
        self.validate_front_and_back_havent_crossed()?;

        if self.front_entry? >= self.entry_slice.len() {
            return None;
        }

        let curr_entry = &self.entry_slice[self.front_entry?];
        let mem_start = self.curr_location_in_front_entry;

        if curr_entry.phys_end - self.curr_location_in_front_entry < self.frame_size {
            self.move_forward_one_entry();
        } else {
            self.curr_location_in_front_entry += self.frame_size;
            if self.curr_location_in_front_entry + self.frame_size > curr_entry.phys_end {
                self.move_forward_one_entry();
            }
        }

        Some(PhysicalAddress::new(mem_start))
    }
}

impl DoubleEndedIterator for FreeFrameIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.validate_front_and_back_havent_crossed()?;

        if self.back_entry? >= self.entry_slice.len() {
            return None;
        }

        let curr_entry = &self.entry_slice[self.back_entry?];
        let mem_start = self.curr_location_in_back_entry;

        if self.curr_location_in_back_entry < self.frame_size {
            self.move_backward_one_entry();
        } else {
            self.curr_location_in_back_entry -= self.frame_size;
            if self.curr_location_in_back_entry < curr_entry.free_start {
                self.move_backward_one_entry();
            }
        }

        Some(PhysicalAddress::new(mem_start))
    }
}

#[derive(Debug)]
#[repr(C)]
pub struct MemoryMapEntry {
    phys_start: usize,
    phys_end: usize,
    free_start: usize,
}

impl MemoryMapEntry {
    pub fn new(phys_start: usize, phys_end: usize) -> Self {
        #[cfg(target_arch = "x86_64")]
        crate::memory::assert_page_aligned(phys_start);
        #[cfg(target_arch = "x86_64")]
        crate::memory::assert_page_aligned(phys_end);
        Self {
            phys_start,
            phys_end,
            free_start: phys_start,
        }
    }

    pub fn phys_start(&self) -> usize {
        self.phys_start
    }

    pub fn phys_end(&self) -> usize {
        self.phys_end
    }

    pub fn free_start(&self) -> usize {
        self.free_start
    }

    pub fn free_size(&self) -> usize {
        self.phys_end - self.free_start
    }
}

#[cfg(all(not(feature = "no-std"), test))]
mod free_frame_iter_tests {
    use super::*;

    #[test]
    fn free_frame_iter_next_handles_empty_slice() {
        let entries = [];
        let mut ff_iter = FreeFrameIter::new(&entries, 1);
        assert!(ff_iter.next().is_none());
    }

    #[test]
    fn free_frame_iter_next_back_handles_empty_slice() {
        let entries = [];
        let mut ff_iter = FreeFrameIter::new(&entries, 1);
        assert!(ff_iter.next_back().is_none());
    }

    #[test]
    fn free_frame_iter_next_handles_basic_entry_correctly() {
        let frame_size = 1;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 0,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);
        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        assert!(ff_iter.next().is_none());
    }

    #[test]
    fn free_frame_iter_next_handles_entry_free_start_correctly() {
        let frame_size = 1;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 1,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        assert!(ff_iter.next().is_none());
    }

    #[test]
    fn free_frame_iter_next_handles_frame_size_correctly() {
        let frame_size = 2;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 0,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 2);

        assert!(ff_iter.next().is_none());
    }

    #[test]
    fn free_frame_iter_next_handles_multiple_entries() {
        let frame_size = 2;
        let entries = [
            MemoryMapEntry {
                phys_start: 0,
                phys_end: frame_size * 2,
                free_start: 0,
            },
            MemoryMapEntry {
                phys_start: frame_size * 4,
                phys_end: frame_size * 6,
                free_start: frame_size * 4,
            },
        ];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 2);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 8);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 10);

        assert!(ff_iter.next().is_none());
    }

    #[test]
    fn free_frame_iter_next_back_handles_basic_entry_correctly() {
        let frame_size = 1;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 0,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);
        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        assert!(ff_iter.next_back().is_none());
    }

    #[test]
    fn free_frame_iter_next_back_handles_entry_free_start_correctly() {
        let frame_size = 1;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 1,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        assert!(ff_iter.next_back().is_none());
    }

    #[test]
    fn free_frame_iter_next_back_handles_frame_size_correctly() {
        let frame_size = 2;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 0,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 2);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        assert!(ff_iter.next_back().is_none());
    }

    #[test]
    fn free_frame_iter_next_back_handles_multiple_entries() {
        let frame_size = 2;
        let entries = [
            MemoryMapEntry {
                phys_start: 0,
                phys_end: frame_size * 2,
                free_start: 0,
            },
            MemoryMapEntry {
                phys_start: frame_size * 4,
                phys_end: frame_size * 6,
                free_start: frame_size * 4,
            },
        ];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 10);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 8);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 2);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        assert!(ff_iter.next_back().is_none());
    }

    #[test]
    fn free_frame_iter_interspersed_next_and_next_back() {
        let frame_size = 2;
        let entries = [
            MemoryMapEntry {
                phys_start: 0,
                phys_end: frame_size * 2,
                free_start: 0,
            },
            MemoryMapEntry {
                phys_start: frame_size * 4,
                phys_end: frame_size * 6,
                free_start: frame_size * 4,
            },
        ];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 10);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 2);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 8);
    }

    #[test]
    fn free_frame_iter_exhausted_forward_iter_leaves_back_exhausted() {
        let frame_size = 1;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 0,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);
        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        assert!(ff_iter.next().is_none());
        assert!(ff_iter.next_back().is_none());
    }

    #[test]
    fn free_frame_iter_exhausted_back_iter_leaves_forward_exhausted() {
        let frame_size = 1;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 2,
            free_start: 0,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);
        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        assert!(ff_iter.next_back().is_none());
        assert!(ff_iter.next().is_none());
    }

    #[test]
    fn free_frame_iter_handles_crossing_front_and_back_ptrs_basic_entry_overlap() {
        let frame_size = 1;
        let entries = [
            MemoryMapEntry {
                phys_start: 0,
                phys_end: frame_size * 2,
                free_start: 0,
            },
            MemoryMapEntry {
                phys_start: frame_size * 2,
                phys_end: frame_size * 3,
                free_start: frame_size * 2,
            },
        ];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);
        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 2);

        assert!(ff_iter.next_back().is_none());
        assert!(ff_iter.next().is_none());
    }

    #[test]
    fn free_frame_iter_handles_crossing_front_and_back_ptrs_entry_memory_region_overlap() {
        let frame_size = 1;
        let entries = [MemoryMapEntry {
            phys_start: 0,
            phys_end: frame_size * 3,
            free_start: 0,
        }];
        let mut ff_iter = FreeFrameIter::new(&entries, frame_size);
        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 0);

        let n = ff_iter.next().expect("iter should be valid");
        assert_eq!(n.into_inner(), 1);

        let n = ff_iter.next_back().expect("iter should be valid");
        assert_eq!(n.into_inner(), 2);

        assert!(ff_iter.next_back().is_none());
        assert!(ff_iter.next().is_none());
    }
}

use core::sync::atomic::Ordering;
use std::sync::Arc;

cfg_if::cfg_if! {
    if #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))] {
        use loom::sync::atomic::AtomicPtr;
    } else {
        use core::sync::atomic::AtomicPtr;
    }
}

/// a tagged pointer uses the unused highest bit in a memory address to store
/// additional metadata
///
/// see more: https://en.wikipedia.org/wiki/Tagged_pointer
// TODO [matthew-russo] wrappig this in an `Arc` feels wrong, need to revisit this
pub struct TaggedPtr<T>(Arc<AtomicPtr<T>>);

impl<T> TaggedPtr<T> {
    const IS_TAGGED: u64 = 0b1;

    /// construct a new TaggedPtr
    pub fn new(t: *mut T) -> Self {
        Self(Arc::new(AtomicPtr::new(t)))
    }

    /// get the raw underlying pointer
    pub fn get_ptr(&self) -> *mut T {
        self.0.load(Ordering::Acquire)
    }

    /// store the provided ptr in the TaggedPtr
    pub fn set_ptr(&self, ptr: *mut T) {
        self.0.store(ptr, Ordering::Release);
    }

    /// copy the pointer out to a new TaggedPtr
    pub fn copy_ptr(&self) -> Self {
        Self(Arc::new(AtomicPtr::new(self.get_ptr())))
    }

    /// compare and swap the underlying pointers
    pub fn cas(&self, expected: *mut T, set_to: *mut T) -> bool {
        self.0
            .compare_exchange_weak(expected, set_to, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
    }

    /// returns true if the TaggedPtr has been tagged
    pub fn is_tagged(&self) -> bool {
        (self.get_ptr() as u64) & Self::IS_TAGGED == Self::IS_TAGGED
    }

    /// returns the pointer with the tag set
    pub fn tagged(&self) -> *mut T {
        ((self.get_ptr() as u64) | Self::IS_TAGGED) as *mut T
    }

    /// returns the pointer without the tag set
    pub fn untagged(&self) -> *mut T {
        ((self.get_ptr() as u64) & !Self::IS_TAGGED) as *mut T
    }

    /// dereference the untagged pointer and immutably borrow the data
    // TODO [matthew-russo] i dont think the 'static is sound
    pub fn deref_untagged(&self) -> &'static T {
        unsafe { &*self.untagged() }
    }

    /// dereference the untagged pointer and mutably borrow the data
    // TODO [matthew-russo] i dont think the 'static is sound
    pub fn deref_untagged_mut(&self) -> &'static mut T {
        unsafe { &mut *self.untagged() }
    }
}

impl<T> Clone for TaggedPtr<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> core::fmt::Debug for TaggedPtr<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!(
            "{{ ptr: {:p}, is_tagged: {} }}",
            self.untagged(),
            self.is_tagged()
        ))
    }
}

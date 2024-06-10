use core::sync::atomic::Ordering;
use std::sync::Arc;

cfg_if::cfg_if! {
    if #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))] {
        use loom::sync::atomic::AtomicPtr;
    } else {
        use core::sync::atomic::AtomicPtr;
    }
}

pub struct TaggedPtr<T>(Arc<AtomicPtr<T>>);

impl<T> TaggedPtr<T> {
    const IS_MARKED_FOR_DELETION: u64 = 0b1;

    pub fn new(t: *mut T) -> Self {
        Self(Arc::new(AtomicPtr::new(t)))
    }

    pub fn get_ptr(&self) -> *mut T {
        self.0.load(Ordering::Acquire)
    }

    pub fn set_ptr(&self, ptr: *mut T) {
        self.0.store(ptr, Ordering::Release);
    }

    pub fn copy_ptr(&self) -> Self {
        Self(Arc::new(AtomicPtr::new(self.get_ptr())))
    }

    pub fn cas(&self, expected: *mut T, set_to: *mut T) -> bool {
        self.0
            .compare_exchange_weak(expected, set_to, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
    }

    pub fn is_marked(&self) -> bool {
        (self.get_ptr() as u64) & Self::IS_MARKED_FOR_DELETION == Self::IS_MARKED_FOR_DELETION
    }

    pub fn marked(&self) -> *mut T {
        ((self.get_ptr() as u64) | Self::IS_MARKED_FOR_DELETION) as *mut T
    }

    pub fn unmarked(&self) -> *mut T {
        ((self.get_ptr() as u64) & !Self::IS_MARKED_FOR_DELETION) as *mut T
    }

    pub unsafe fn deref(&self) -> &'static T {
        &*self.unmarked()
    }

    pub unsafe fn deref_mut(&self) -> &'static mut T {
        &mut *self.unmarked()
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
            "{{ ptr: {:p}, is_marked: {} }}",
            self.unmarked(),
            self.is_marked()
        ))
    }
}

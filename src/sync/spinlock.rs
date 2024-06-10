use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicBool, Ordering};

const LOCKED: bool = true;
const UNLOCKED: bool = false;

pub struct Spinlock<T> {
    is_locked: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for Spinlock<T> {}
unsafe impl<T: Send> Sync for Spinlock<T> {}

impl<T> Spinlock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            is_locked: AtomicBool::new(UNLOCKED),
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> SpinlockGuard<'_, T> {
        while self
            .is_locked
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::AcqRel, Ordering::Relaxed)
            .is_err()
        {
            while self.is_locked.load(Ordering::Relaxed) == LOCKED {
                core::hint::spin_loop();
            }
        }

        SpinlockGuard { lock: self }
    }

    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }

    fn unlock(&self) {
        self.is_locked.store(UNLOCKED, Ordering::Release);
    }

    pub fn raw_lock(&self) -> RawSpinlockGuard<'_, T> {
        while self
            .is_locked
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::AcqRel, Ordering::Relaxed)
            .is_err()
        {
            while self.is_locked.load(Ordering::Relaxed) == LOCKED {
                core::hint::spin_loop();
            }
        }

        RawSpinlockGuard { lock: self }
    }

    /// # Safety
    /// - must not be called if the caller does not currently hold the lock
    /// - must not be called if there are any existing SpinlockGuard's for the lock
    pub unsafe fn raw_unlock(&self) {
        self.unlock();
    }
}

/// SpinlockGuard provides safe access to the data behind a Spinlock. It follows
/// RAII idioms and unlocks the lock when its dropped.
pub struct SpinlockGuard<'a, T> {
    lock: &'a Spinlock<T>,
}

impl<'a, T> Deref for SpinlockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> DerefMut for SpinlockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T> Drop for SpinlockGuard<'a, T> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

/// RawSpinlockGaurd provides access to the data behind a Spinlock but unlike its
/// safer variant [`SpinlockGuard`], [`RawSpinlockGuard`] does not unlock the lock
/// when its dropped. It is primarily used in low-level syncrhonization primitives
/// where the locker and unlockers are two different Tasks with a context switch
/// in between.
pub struct RawSpinlockGuard<'a, T> {
    lock: &'a Spinlock<T>,
}

impl<'a, T> Deref for RawSpinlockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> DerefMut for RawSpinlockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

#[cfg(test)]
mod test {
    use std::sync::Arc;

    use super::*;

    struct MyStruct {
        u: u32,
    }

    impl MyStruct {
        fn add_one(&mut self) {
            self.u += 1;
        }
    }

    #[test]
    fn smoke_test_serial() {
        let u = 73;
        let spin = Spinlock::new(MyStruct { u });
        {
            let mut ms_guard = spin.lock();
            ms_guard.add_one();
        }
        assert_eq!(spin.into_inner().u, u + 1);
    }

    #[test]
    fn smoke_test_parallel() {
        let u = 73;
        let spin = Arc::new(Spinlock::new(MyStruct { u }));

        let num_threads = 4;
        let num_ops = 100;

        let mut threads = Vec::with_capacity(num_threads);
        for _thread_num in 0..num_threads {
            let spin = spin.clone();
            threads.push(std::thread::spawn(move || {
                for _op_num in 0..num_ops {
                    let mut ms_guard = spin.lock();
                    ms_guard.add_one();
                }
            }));
        }

        for thread in threads {
            thread.join().unwrap();
        }

        let ms_guard = spin.lock();
        assert_eq!(ms_guard.u, u + (num_threads * num_ops) as u32);
    }
}

use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicBool, Ordering};

/// a channel that supports sending a single value
pub struct Oneshot<T> {
    message: UnsafeCell<MaybeUninit<T>>,
    in_use: AtomicBool,
    ready: AtomicBool,
}

unsafe impl<T> Sync for Oneshot<T> where T: Send {}

impl<T> Oneshot<T> {
    /// construct a new Oneshot
    pub const fn new() -> Self {
        Self {
            message: UnsafeCell::new(MaybeUninit::uninit()),
            in_use: AtomicBool::new(false),
            ready: AtomicBool::new(false),
        }
    }

    /// sends a message on the oneshot
    ///
    /// # Panics
    /// - if a message has already been sent
    pub fn send(&self, message: T) {
        if self.in_use.swap(true, Ordering::Relaxed) {
            panic!(
                "Oneshot::send called multiple times before Oneshot::receive, breaking a safety invaraint"
            );
        }
        // Safety: we just checked and set the in_use flag, preventing any other
        // threads from making it to this point.
        unsafe { (*self.message.get()).write(message) };
        self.ready.store(true, Ordering::Release);
    }

    /// checks whether a message is ready to be received
    pub fn is_ready(&self) -> bool {
        self.ready.load(Ordering::Relaxed)
    }

    /// receives the message from the oneshot
    ///
    /// use `Oneshot::is_ready` to check if the message is ready to be received.
    ///
    /// # Panics
    /// - if no message is available
    /// - if receive has already been called
    pub fn receive(&self) -> T {
        if !self.ready.swap(false, Ordering::Acquire) {
            panic!("Oneshot::receive called before Oneshot::send, breaking a safety invariant");
        }
        // Safety: we just checked and reset the ready flag
        unsafe { (*self.message.get()).assume_init_read() }
    }
}

impl<T> Default for Oneshot<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for Oneshot<T> {
    fn drop(&mut self) {
        if *self.ready.get_mut() {
            // Safety: if the ready flag is set, `Oneshot::send` was called but
            // `Oneshot::receive` was not.
            unsafe { self.message.get_mut().assume_init_drop() };
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MyStruct {
        u: u32,
        s: String,
    }

    #[test]
    fn can_send() {
        let c = Oneshot::new();
        c.send(MyStruct {
            u: 42,
            s: "hello world".to_string(),
        });
    }

    #[test]
    fn is_ready_is_set_during_send() {
        let c = Oneshot::new();
        assert!(!c.is_ready());
        c.send(MyStruct {
            u: 42,
            s: "hello world".to_string(),
        });
        assert!(c.is_ready());
    }

    #[test]
    fn can_receive() {
        let ms1 = MyStruct {
            u: 42,
            s: "hello world".to_string(),
        };
        let c = Oneshot::new();
        c.send(ms1.clone());
        let ms2 = c.receive();
        assert_eq!(ms1, ms2);
    }

    #[test]
    #[should_panic]
    fn calling_send_multiple_times_panics() {
        let c = Oneshot::new();
        c.send(MyStruct {
            u: 42,
            s: "hello world".to_string(),
        });
        c.send(MyStruct {
            u: 42,
            s: "hello world".to_string(),
        });
    }

    #[test]
    #[should_panic]
    fn calling_receive_before_send_panics() {
        let c: Oneshot<MyStruct> = Oneshot::new();
        c.receive();
    }

    #[test]
    #[should_panic]
    fn calling_receive_multiple_times_panics() {
        let c = Oneshot::new();
        c.send(MyStruct {
            u: 42,
            s: "hello world".to_string(),
        });
        c.receive();
        c.receive();
    }

    #[test]
    fn dropping_channel_after_sending_before_receiving_cleans_up_sent_data() {
        static WAS_DROPPED: AtomicBool = AtomicBool::new(false);

        struct DropTracker;

        impl Drop for DropTracker {
            fn drop(&mut self) {
                WAS_DROPPED.store(true, Ordering::Relaxed);
            }
        }

        let c = Oneshot::new();
        c.send(DropTracker);
        drop(c);
        assert!(WAS_DROPPED.load(Ordering::Relaxed));
    }
}

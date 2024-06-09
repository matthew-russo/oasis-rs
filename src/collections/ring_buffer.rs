use core::mem::MaybeUninit;

pub type RingBufferResult<T> = Result<T, RingBufferError>;

#[derive(Debug)]
pub enum RingBufferError {
    NoCapacity,
}

pub struct RingBuffer<T, const N: usize> {
    inner: [MaybeUninit<T>; N],
    writer: usize,
    reader: usize,
    in_use: usize,
}

impl<T, const N: usize> RingBuffer<T, N> {
    pub fn new() -> Self {
        Self {
            // Safety: The `assume_init` is safe because the type we are
            // claiming to have initialized here is a bunch of `MaybeUninit`s,
            // which do not require initialization.
            // https://doc.rust-lang.org/beta/core/mem/union.MaybeUninit.html#initializing-an-array-element-by-element
            inner: unsafe { MaybeUninit::uninit().assume_init() },
            writer: 0,
            reader: 0,
            in_use: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.in_use
    }

    pub const fn capacity(&self) -> usize {
        N
    }

    pub fn free_space(&self) -> usize {
        N - self.in_use
    }

    pub fn is_empty(&self) -> bool {
        self.in_use == 0
    }

    pub fn push(&mut self, data: T) -> RingBufferResult<()> {
        if self.in_use >= N {
            return Err(RingBufferError::NoCapacity);
        }

        self.inner[self.writer].write(data);
        self.in_use += 1;
        self.writer += 1;
        if self.writer >= N {
            self.writer = 0;
        }

        Ok(())
    }

    pub fn peek(&mut self) -> Option<&T> {
        if self.in_use == 0 {
            return None;
        }
        // Safety : if reader doesn't equal writer, then the reader must be behind
        // the writer who has already written this value
        let t = unsafe { self.inner[self.reader].assume_init_ref() };
        Some(t)
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.in_use == 0 {
            return None;
        }
        let t = core::mem::replace(&mut self.inner[self.reader], MaybeUninit::uninit());
        // Safety : if reader doesn't equal writer, then the reader must be behind
        // the writer who has already written this value
        let t = unsafe { t.assume_init() };
        self.in_use -= 1;
        self.reader += 1;
        if self.reader >= N {
            self.reader = 0;
        }
        Some(t)
    }
}

impl<T, const N: usize> Default for RingBuffer<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    struct MyTestStruct {
        i: i32,
        name: &'static str,
    }

    #[test]
    fn capacity_returns_const_size() {
        const N: usize = 8;
        let rb = RingBuffer::<u32, N>::new();
        assert_eq!(rb.capacity(), N);
    }

    #[test]
    fn peek_on_empty_ringbuffer_returns_none() {
        let mut rb = RingBuffer::<u32, 8>::new();
        assert_eq!(rb.peek(), None);
    }

    #[test]
    fn pop_on_empty_ringbuffer_returns_none() {
        let mut rb = RingBuffer::<u32, 8>::new();
        assert_eq!(rb.pop(), None);
    }

    #[test]
    fn can_push_in_to_ringbuffer() {
        let mut rb = RingBuffer::<u32, 8>::new();
        rb.push(73).expect("failed to push");
    }

    #[test]
    fn can_peek_in_to_ringbuffer() {
        let mut rb = RingBuffer::<u32, 8>::new();
        rb.push(73).expect("failed to push");
        assert_eq!(rb.peek(), Some(&73));
    }

    #[test]
    fn can_pop_from_ringbuffer() {
        let mut rb = RingBuffer::<u32, 8>::new();
        rb.push(73).expect("failed to push");
        assert_eq!(rb.pop(), Some(73));
    }

    #[test]
    fn is_empty_is_only_true_when_no_elements() {
        let mut rb = RingBuffer::<u32, 8>::new();
        assert!(rb.is_empty());
        rb.push(73).expect("failed to push");
        assert!(!rb.is_empty());
        assert_eq!(rb.pop(), Some(73));
        assert!(rb.is_empty());
    }

    #[test]
    fn push_increases_len() {
        let mut rb = RingBuffer::<u32, 8>::new();
        rb.push(73).expect("failed to push");
        assert_eq!(rb.len(), 1);
        rb.push(42).expect("failed to push");
        assert_eq!(rb.len(), 2);
    }

    #[test]
    fn pop_decreases_len() {
        let mut rb = RingBuffer::<u32, 8>::new();
        rb.push(73).expect("failed to push");
        assert_eq!(rb.len(), 1);
        rb.push(42).expect("failed to push");
        assert_eq!(rb.len(), 2);
        rb.pop().expect("failed to pop");
        assert_eq!(rb.len(), 1);
    }

    #[test]
    fn peek_doesnt_remove_entries_and_keeps_len_same() {
        let mut rb = RingBuffer::<u32, 8>::new();
        rb.push(73).expect("failed to push");
        assert_eq!(rb.len(), 1);
        rb.push(42).expect("failed to push");
        assert_eq!(rb.len(), 2);
        assert_eq!(rb.peek().expect("failed to peek"), &73);
        assert_eq!(rb.len(), 2);
        assert_eq!(rb.peek().expect("failed to peek"), &73);
        assert_eq!(rb.len(), 2);
    }

    #[test]
    fn push_when_full_results_in_err() {
        const N: usize = 2;
        let mut rb = RingBuffer::<u32, N>::new();
        for _ in 0..N {
            rb.push(73).expect("failed to push");
        }
        let res = rb.push(73);
        assert!(matches!(res, Err(RingBufferError::NoCapacity)));
    }

    #[test]
    fn smoke_test() {
        let mut rb = RingBuffer::<MyTestStruct, 3>::new();
        let ms1 = MyTestStruct {
            i: 1,
            name: "peter",
        };
        let ms2 = MyTestStruct {
            i: 2,
            name: "paul",
        };
        let ms3 = MyTestStruct {
            i: 3,
            name: "mary",
        };
        let ms4 = MyTestStruct { i: 4, name: "john" };
        rb.push(ms1.clone()).expect("failed to push");
        rb.push(ms2.clone()).expect("failed to push");
        rb.push(ms3.clone()).expect("failed to push");
        rb.push(ms4.clone()).expect_err("should be full capacity");

        assert_eq!(rb.peek().expect("failed to peek"), &ms1);
        assert_eq!(rb.pop().expect("failed to pop"), ms1);

        rb.push(ms4.clone()).expect("should no have capacity");

        assert_eq!(rb.pop().expect("failed to pop"), ms2);
        assert_eq!(rb.pop().expect("failed to pop"), ms3);
        assert_eq!(rb.pop().expect("failed to pop"), ms4);
        assert_eq!(rb.pop(), None);
    }
}

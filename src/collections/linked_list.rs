use core::mem::MaybeUninit;

/// a non-allocating, circular doubly-linked list, usable in no-std environments as the
/// caller is expected to handle allocations and frees
pub struct LinkedList<T> {
    /// a sentinel node that always exists, even in empty lists
    sentinel: *mut LinkedListNode<T>,
    /// the number of non-sentinel elements in the list
    len: usize,
}

impl<T> LinkedList<T> {
    /// create a new LinkedList, using the provided storage for the sentinel node
    pub fn new(sentinel_ptr: &mut MaybeUninit<LinkedListNode<T>>) -> Self {
        LinkedListNode::init_sentinel(sentinel_ptr);
        Self {
            sentinel: sentinel_ptr.as_mut_ptr(),
            len: 0,
        }
    }

    /// get the length of the list, not including the sentinel node
    pub fn len(&self) -> usize {
        self.len
    }

    /// returns true if the length of the list is 0
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// get the first element of the list after the sentinel, or None if the list
    /// is empty
    pub fn head(&self) -> Option<*mut LinkedListNode<T>> {
        if self.len == 0 {
            None
        } else {
            // SAFETY: we validated that our list is not empty
            unsafe { Some((*self.sentinel).next()) }
        }
    }
    /// get the first element of the list before the sentinel, or None if the list
    /// is empty
    pub fn tail(&self) -> Option<*mut LinkedListNode<T>> {
        if self.len == 0 {
            None
        } else {
            // SAFETY: we validated that our list is not empty
            unsafe { Some((*self.sentinel).prev()) }
        }
    }

    /// push a node to the front of this list. the provided node must be
    /// initialized and be at a stable location in storage
    /// # Safety
    /// `n` must point to a valid LinkedListNode<T>
    pub unsafe fn push_front(&mut self, n: *mut LinkedListNode<T>) {
        if self.is_empty() {
            (*self.sentinel).set_next(n);
            (*self.sentinel).set_prev(n);
            (*n).set_next(self.sentinel);
            (*n).set_prev(self.sentinel);
        } else {
            (*self.sentinel).insert_after(n);
        }

        self.len += 1;
    }

    /// push a node to the back of this list. the provided node must be
    /// initialized and be at a stable location in storage
    /// # Safety
    /// `n` must point to a valid LinkedListNode<T>
    pub unsafe fn push_back(&mut self, n: *mut LinkedListNode<T>) {
        if self.is_empty() {
            (*self.sentinel).set_next(n);
            (*self.sentinel).set_prev(n);
            (*n).set_next(self.sentinel);
            (*n).set_prev(self.sentinel);
        } else {
            (*self.sentinel).insert_before(n);
        }

        self.len += 1;
    }

    /// pop a node from the front of this list. if the list is empty, None, is
    /// returned. the caller is responsible for freeing any underlying storage
    /// of the node.
    /// # Safety
    /// `self` must be a valid LinkedList
    pub unsafe fn pop_front(&mut self) -> Option<*mut LinkedListNode<T>> {
        if self.len == 0 {
            None
        } else {
            let to_return = (*self.sentinel).next();
            let new_head = (*to_return).next();
            assert!(!new_head.is_null());
            (*self.sentinel).set_next(new_head);
            (*new_head).set_prev(self.sentinel);
            (*to_return).set_prev(core::ptr::null_mut());
            (*to_return).set_next(core::ptr::null_mut());
            self.len -= 1;
            Some(to_return)
        }
    }

    /// pop a node from the back of this list. if the list is empty, None, is
    /// returned. the caller is responsible for freeing any underlying storage
    /// of the node.
    /// # Safety
    /// `self` must be a valid LinkedList
    pub unsafe fn pop_back(&mut self) -> Option<*mut LinkedListNode<T>> {
        if self.len == 0 {
            None
        } else {
            let to_return = (*self.sentinel).prev();
            let new_tail = (*to_return).prev();
            assert!(!new_tail.is_null());
            (*self.sentinel).set_prev(new_tail);
            (*new_tail).set_next(self.sentinel);
            (*to_return).set_prev(core::ptr::null_mut());
            (*to_return).set_next(core::ptr::null_mut());
            self.len -= 1;
            Some(to_return)
        }
    }

    /// appends another list to the end of `self`. we will always use
    /// `self`'s sentinel for the the resulting list, returning a pointer to
    /// `other`'s sentinel that the caller is expected to clean up as
    /// necessary.
    ///
    /// # Safety
    /// `self` and `other` must be valid LinkedLists
    pub unsafe fn append(&mut self, other: LinkedList<T>) -> *mut LinkedListNode<T> {
        // we need to
        // - patch our actual tail to point its next to the head of other
        // - patch others actual head to point its prev to the tail of self
        // - patch our sentinel prev to the tail of other
        // - patch our sentinel next to the head of self

        if self.is_empty() && other.is_empty() {
            // nothing to do
        } else if self.is_empty() {
            let other_head = (*other.sentinel).next();
            let other_tail = (*other.sentinel).prev();
            (*self.sentinel).set_next(other_head);
            (*self.sentinel).set_prev(other_tail);
            (*other_head).set_prev(self.sentinel);
            (*other_tail).set_next(self.sentinel);
        } else {
            let other_head = (*other.sentinel).next();
            let other_tail = (*other.sentinel).prev();
            let curr_tail = (*self.sentinel).prev();
            (*curr_tail).insert_after(other_head);
            (*self.sentinel).set_prev(other_tail);
            (*other_tail).set_next(self.sentinel);
        }

        self.len += other.len();

        // sentinel pointers are special in that they may not be allocated
        // from the global allocator to allow systems to bootstrap before they
        // have a system allocator so in this situation we just return the
        // pointer and the caller can decide if/how to free it
        other.sentinel
    }

    /// prepends another list to the beginning of `self`. we will always use
    /// `self`'s sentinel for the resulting list, returning a pointer to
    /// `other`'s sentinel that the caller is expected to clean up as
    /// necessary.
    ///
    /// # Safety
    /// `self` and `other` must be valid LinkedLists
    pub unsafe fn prepend(&mut self, other: LinkedList<T>) -> *mut LinkedListNode<T> {
        // we need to
        // - patch our actual head to point its prev to the tail of other
        // - patch others actual tail to point its next to the head of self
        // - patch our sentinel prev to the tail of other
        // - patch our sentinel next to the head of self

        if other.is_empty() {
            // nothing to do
        } else if self.is_empty() {
            let other_head = (*other.sentinel).next();
            let other_tail = (*other.sentinel).prev();
            (*self.sentinel).set_next(other_head);
            (*self.sentinel).set_prev(other_tail);
            (*other_head).set_prev(self.sentinel);
            (*other_tail).set_next(self.sentinel);
        } else {
            let other_head = (*other.sentinel).next();
            let other_tail = (*other.sentinel).prev();
            let curr_head = (*self.sentinel).next();
            (*curr_head).insert_before(other_tail);
            (*self.sentinel).set_next(other_head);
            (*other_head).set_prev(self.sentinel);
        }

        self.len += other.len();

        // sentinel pointers are special in that they may not be allocated
        // from the global allocator to allow systems to bootstrap before they
        // have a system allocator so in this situation we just return the
        // pointer and the caller can decide if/how to free it
        other.sentinel
    }

    /// return an immutable iterator for this list
    pub fn iter(&self) -> LinkedListIter<'_, T> {
        LinkedListIter {
            _ll: self,
            curr: unsafe { (*self.sentinel).next() },
        }
    }

    /// return a mutable iterator for this list
    pub fn iter_mut(&mut self) -> LinkedListIterMut<'_, T> {
        LinkedListIterMut {
            _ll: self,
            curr: unsafe { (*self.sentinel).next() },
        }
    }

    /// return a cursor for this list
    pub fn cursor(&mut self) -> LinkedListCursor<'_, T> {
        LinkedListCursor::new(self)
    }
}

// TODO [matthew-russo] i don't know if this is sound
unsafe impl<T: Send> Send for LinkedList<T> {}

/// a node in the linked list, a public container that hides internal details
/// of node layout
pub struct LinkedListNode<T> {
    internal: InternalLinkedListNode<T>,
}

impl<T> LinkedListNode<T> {
    /// initialize the sentinel node
    fn init_sentinel(sentinel_ptr: &mut MaybeUninit<LinkedListNode<T>>) {
        sentinel_ptr.write(LinkedListNode {
            internal: InternalLinkedListNode::Sentinel {
                prev: core::ptr::null_mut(),
                next: core::ptr::null_mut(),
            },
        });
    }

    /// returns true if the node is the sentinel node
    fn is_sentinel(&self) -> bool {
        match &self.internal {
            InternalLinkedListNode::Sentinel { .. } => true,
            InternalLinkedListNode::Data { .. } => false,
        }
    }

    /// constructs a new node given the provided value
    pub const fn new(t: T) -> Self {
        Self {
            internal: InternalLinkedListNode::new_data(t),
        }
    }

    /// immutably borrow the internal data of the node
    pub fn data(&self) -> &T {
        match &self.internal {
            InternalLinkedListNode::Sentinel { .. } => {
                unreachable!("LinkedList implementation will never vend Sentinels")
            }
            InternalLinkedListNode::Data { data, .. } => data,
        }
    }

    /// mutably borrow the internal data of the node
    pub fn data_mut(&mut self) -> &mut T {
        match &mut self.internal {
            InternalLinkedListNode::Sentinel { .. } => {
                unreachable!("LinkedList implementation will never vend Sentinels")
            }
            InternalLinkedListNode::Data { data, .. } => data,
        }
    }

    /// peek if the next node is present and return an immutable
    /// reference to its data
    pub fn peek_next_data(&self) -> Option<&T> {
        assert!(!self.next().is_null());
        match unsafe { &(*self.next()).internal } {
            InternalLinkedListNode::Sentinel { .. } => None,
            InternalLinkedListNode::Data { data, .. } => Some(data),
        }
    }

    /// peek if the next node is present and return an immutable
    /// reference to its data
    pub fn peek_prev_data(&self) -> Option<&T> {
        assert!(!self.prev().is_null());
        match unsafe { &(*self.prev()).internal } {
            InternalLinkedListNode::Sentinel { .. } => None,
            InternalLinkedListNode::Data { data, .. } => Some(data),
        }
    }

    /// insert the provided node before the current node
    /// # Safety
    /// `node` must be a valid LinkedListNode<T>
    // Before: (self.prev) <-> (self) <-> (self.next)
    // After: (self.prev) <-> (n) <-> (self) <-> (self.next)
    unsafe fn insert_before(&mut self, node: *mut LinkedListNode<T>) {
        assert!(!self.prev().is_null());

        let curr_prev = self.prev();
        (*curr_prev).set_next(node);

        let n = &mut *node;
        n.set_prev(curr_prev);
        n.set_next(core::ptr::addr_of_mut!(*self));

        self.set_prev(node);
    }

    /// insert the provided node after the current node
    /// # Safety
    /// `node` must be a valid LinkedListNode<T>
    // Before: (self.prev) <-> (self) <-> (self.next)
    // After: (self.prev) <-> (self) <-> (n) <-> (self.next)
    unsafe fn insert_after(&mut self, node: *mut LinkedListNode<T>) {
        assert!(!self.prev().is_null());

        let curr_next = self.next();
        (*curr_next).set_prev(node);

        let n = &mut *node;
        n.set_prev(core::ptr::addr_of_mut!(*self));
        n.set_next(curr_next);

        self.set_next(node);
    }

    /// Remove self from whatever list it is in, leaving self.prev linked with
    /// self.next
    fn unlink_self(&mut self) {
        match &mut self.internal {
            InternalLinkedListNode::Sentinel { .. } => {
                unreachable!("LinkedList implementation will never vend Sentinels")
            }
            InternalLinkedListNode::Data { prev, next, .. } => {
                unsafe { (**prev).set_next(*next) };
                unsafe { (**next).set_prev(*prev) };
                *prev = core::ptr::null_mut();
                *next = core::ptr::null_mut();
            }
        }
    }

    fn prev(&self) -> *mut LinkedListNode<T> {
        self.internal.prev()
    }

    fn next(&self) -> *mut LinkedListNode<T> {
        self.internal.next()
    }

    fn set_prev(&mut self, new_prev: *mut LinkedListNode<T>) {
        self.internal.set_prev(new_prev);
    }

    fn set_next(&mut self, new_next: *mut LinkedListNode<T>) {
        self.internal.set_next(new_next);
    }
}

unsafe impl<T: Send> Send for LinkedListNode<T> {}

impl<T: core::fmt::Debug> core::fmt::Debug for LinkedListNode<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.internal {
            InternalLinkedListNode::Sentinel { .. } => f
                .debug_struct("Node")
                .field("prev", &self.prev())
                .field("self", &core::ptr::addr_of!(*self))
                .field("next", &self.next())
                .finish(),
            InternalLinkedListNode::Data { .. } => f
                .debug_struct("Node")
                .field("prev", &self.prev())
                .field("self", &core::ptr::addr_of!(*self))
                .field("data", &self.data())
                .field("next", &self.next())
                .finish(),
        }
    }
}

/// the private internal layout of a node, either a sentinel or user-provided data
enum InternalLinkedListNode<T> {
    Sentinel {
        prev: *mut LinkedListNode<T>,
        next: *mut LinkedListNode<T>,
    },
    Data {
        prev: *mut LinkedListNode<T>,
        data: T,
        next: *mut LinkedListNode<T>,
    },
}

impl<T> InternalLinkedListNode<T> {
    const fn new_data(data: T) -> Self {
        Self::Data {
            prev: core::ptr::null_mut(),
            data,
            next: core::ptr::null_mut(),
        }
    }

    fn prev(&self) -> *mut LinkedListNode<T> {
        match self {
            Self::Sentinel { prev, .. } | Self::Data { prev, .. } => *prev,
        }
    }

    fn next(&self) -> *mut LinkedListNode<T> {
        match self {
            Self::Sentinel { next, .. } | Self::Data { next, .. } => *next,
        }
    }

    fn set_prev(&mut self, new_prev: *mut LinkedListNode<T>) {
        match self {
            Self::Sentinel { ref mut prev, .. } | Self::Data { ref mut prev, .. } => {
                *prev = new_prev
            }
        }
    }

    fn set_next(&mut self, new_next: *mut LinkedListNode<T>) {
        match self {
            Self::Sentinel { ref mut next, .. } | Self::Data { ref mut next, .. } => {
                *next = new_next
            }
        }
    }
}

pub struct LinkedListIter<'a, T> {
    _ll: &'a LinkedList<T>,
    curr: *mut LinkedListNode<T>,
}

impl<'a, T> Iterator for LinkedListIter<'a, T> {
    type Item = &'a LinkedListNode<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr.is_null() {
            return None;
        }

        // # Safety
        // we just validated `self.curr` is not null
        unsafe {
            let to_return = &(*self.curr);

            match to_return.internal {
                InternalLinkedListNode::Sentinel { .. } => None,
                InternalLinkedListNode::Data { .. } => {
                    self.curr = to_return.next();
                    Some(to_return)
                }
            }
        }
    }
}

pub struct LinkedListIterMut<'a, T> {
    _ll: &'a LinkedList<T>,
    curr: *mut LinkedListNode<T>,
}

impl<'a, T> Iterator for LinkedListIterMut<'a, T> {
    type Item = &'a mut LinkedListNode<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr.is_null() {
            return None;
        }

        // # Safety
        // we just validated `self.curr` is not null
        unsafe {
            let to_return = &mut (*self.curr);

            match to_return.internal {
                InternalLinkedListNode::Sentinel { .. } => None,
                InternalLinkedListNode::Data { .. } => {
                    self.curr = to_return.next();
                    Some(to_return)
                }
            }
        }
    }
}

pub struct LinkedListCursor<'a, T> {
    ll: &'a mut LinkedList<T>,
    curr: *mut LinkedListNode<T>,
}

impl<'a, T> LinkedListCursor<'a, T> {
    fn new(ll: &'a mut LinkedList<T>) -> Self {
        let curr = ll.sentinel;
        Self { ll, curr }
    }

    /// get the data of the current node or None if the current node is the
    /// sentinel
    pub fn curr_data(&self) -> Option<&T> {
        let curr = unsafe { &*self.curr };
        if !curr.is_sentinel() {
            Some(curr.data())
        } else {
            None
        }
    }

    /// get the data of the current node or None if the current node is the
    /// sentinel
    pub fn curr_data_mut(&mut self) -> Option<&mut T> {
        let curr = unsafe { &mut *self.curr };
        if !curr.is_sentinel() {
            Some(curr.data_mut())
        } else {
            None
        }
    }

    /// move the cursor backward one element
    pub fn move_prev(&mut self) {
        let curr = unsafe { &*self.curr };
        if curr.is_sentinel() {
            if !curr.prev().is_null() {
                self.curr = curr.prev();
            } else {
                // the sentinel can only have a null ptr if its
                // empty, this is just a defense in depth check
                assert!(self.ll.is_empty());
            }
        } else {
            // only a sentinel in an empty list may have a null ptr,
            // this is just a defense in depth check
            assert!(!curr.prev().is_null());
            self.curr = curr.prev();
        }
    }

    /// move the cursor forward one element
    pub fn move_next(&mut self) {
        let curr = unsafe { &*self.curr };
        if curr.is_sentinel() {
            if !curr.next().is_null() {
                self.curr = curr.next();
            } else {
                // the sentinel can only have a null ptr if its
                // empty, this is just a defense in depth check
                assert!(self.ll.is_empty());
            }
        } else {
            // only a sentinel in an empty list may have a null ptr,
            // this is just a defense in depth check
            assert!(!curr.next().is_null());
            self.curr = curr.next();
        }
    }

    /// if the current node is the sentinel, do nothing
    ///
    /// if the current node is data, remove node from the list, reducing the
    /// size of the list by 1, advancing the cursor forward and returning
    /// the removed node.
    pub fn remove_curr(&mut self) -> Option<*mut LinkedListNode<T>> {
        if self.curr.is_null() {
            return None;
        }

        unsafe {
            if (*self.curr).is_sentinel() {
                return None;
            }

            let to_return = self.curr;
            let next = (*self.curr).next();
            (*self.curr).unlink_self();
            self.curr = next;
            self.ll.len -= 1;
            Some(to_return)
        }
    }

    /// insert the provided node before the currently pointed at node,
    /// increasing the size of the list by 1. The cursor will not move.
    ///
    /// # Safety
    /// `new_node` must be a valid pointer to a LinkedListNode<T>
    pub unsafe fn insert_before_curr(&mut self, new_node: *mut LinkedListNode<T>) {
        if self.ll.is_empty() {
            (*self.ll.sentinel).set_next(new_node);
            (*self.ll.sentinel).set_prev(new_node);
            (*new_node).set_next(self.ll.sentinel);
            (*new_node).set_prev(self.ll.sentinel);
        } else {
            (*self.curr).insert_before(new_node);
        }

        // (*self.curr).insert_before(new_node);
        self.ll.len += 1;
    }

    /// insert the provided node after the currently pointed at node, increasing
    /// the size of the list by 1. The cursor will not move.
    /// # Safety
    /// `new_node` must be a valid pointer to a LinkedListNode<T>
    pub unsafe fn insert_after_curr(&mut self, new_node: *mut LinkedListNode<T>) {
        if self.ll.is_empty() {
            (*self.ll.sentinel).set_next(new_node);
            (*self.ll.sentinel).set_prev(new_node);
            (*new_node).set_next(self.ll.sentinel);
            (*new_node).set_prev(self.ll.sentinel);
        } else {
            (*self.curr).insert_after(new_node);
        }
        // (*self.curr).insert_after(new_node);
        self.ll.len += 1;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn linked_list_nodes_are_sendable() {
        fn send<S: Send>(_: S) {}
        send(LinkedListNode::new(42));
    }

    #[test]
    fn linked_lists_are_sendable() {
        fn send<S: Send>(_: S) {}
        let mut sentinel_ptr = MaybeUninit::uninit();
        let ll = LinkedList::<u32>::new(&mut sentinel_ptr);
        send(ll);
    }

    #[test]
    fn head_on_empty_list_returns_none() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let ll = LinkedList::<u32>::new(&mut sentinel_ptr);
        assert!(ll.head().is_none());
    }

    #[test]
    fn tail_on_empty_list_returns_none() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let ll = LinkedList::<u32>::new(&mut sentinel_ptr);
        assert!(ll.tail().is_none());
    }

    #[test]
    fn can_push_front() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            assert_eq!(ll.len(), 0);
            ll.push_front(core::ptr::addr_of_mut!(a));
            assert_eq!(ll.len(), 1);
        }
    }

    #[test]
    fn can_push_back() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            assert_eq!(ll.len(), 0);
            ll.push_back(core::ptr::addr_of_mut!(a));
            assert_eq!(ll.len(), 1);
        }
    }

    #[test]
    fn head_after_push_front_returns_some() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);
        let an = 73;
        let mut a = LinkedListNode::new(an);
        unsafe {
            ll.push_front(core::ptr::addr_of_mut!(a));
        }
        let head = ll.head().expect("head should be some after pushing");
        unsafe {
            assert_eq!((*head).data(), &an);
        }
    }

    #[test]
    fn head_after_push_back_returns_some() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);
        let an = 73;
        let mut a = LinkedListNode::new(an);
        unsafe {
            ll.push_back(core::ptr::addr_of_mut!(a));
        }
        let head = ll.head().expect("head should be some after pushing");
        unsafe {
            assert_eq!((*head).data(), &an);
        }
    }

    #[test]
    fn tail_after_push_front_returns_some() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);
        let an = 73;
        let mut a = LinkedListNode::new(an);
        unsafe {
            ll.push_front(core::ptr::addr_of_mut!(a));
        }
        let tail = ll.tail().expect("tail should be some after pushing");
        unsafe {
            assert_eq!((*tail).data(), &an);
        }
    }

    #[test]
    fn tail_after_push_back_returns_some() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);
        let an = 73;
        let mut a = LinkedListNode::new(an);
        unsafe {
            ll.push_back(core::ptr::addr_of_mut!(a));
        }
        let tail = ll.tail().expect("tail should be some after pushing");
        unsafe {
            assert_eq!((*tail).data(), &an);
        }
    }

    #[test]
    fn can_pop_front_after_pushing_front() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            assert_eq!(ll.len(), 0);
            ll.push_front(core::ptr::addr_of_mut!(a));
            let aa = ll.pop_front().expect("failed to pop_front");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);
        }
    }

    #[test]
    fn can_pop_front_after_pushing_back() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            assert_eq!(ll.len(), 0);
            ll.push_back(core::ptr::addr_of_mut!(a));
            let aa = ll.pop_front().expect("failed to pop_front");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);
        }
    }

    #[test]
    fn can_pop_back_after_pushing_front() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            assert_eq!(ll.len(), 0);
            ll.push_front(core::ptr::addr_of_mut!(a));
            let aa = ll.pop_back().expect("failed to pop_back");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);
        }
    }

    #[test]
    fn can_pop_back_after_pushing_back() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            assert_eq!(ll.len(), 0);
            ll.push_back(core::ptr::addr_of_mut!(a));
            let aa = ll.pop_back().expect("failed to pop_back");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);
        }
    }

    #[test]
    fn can_push_front_push_front_pop_front_pop_front() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            let bn = 42;
            let mut b = LinkedListNode::new(bn);
            assert_eq!(ll.len(), 0);
            ll.push_front(core::ptr::addr_of_mut!(a));
            ll.push_front(core::ptr::addr_of_mut!(b));

            let bb = ll.pop_front().expect("failed to pop_front");
            assert_eq!(bb, core::ptr::addr_of_mut!(b));
            assert_eq!(*(*bb).data(), bn);

            let aa = ll.pop_front().expect("failed to pop_front");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);
        }
    }

    #[test]
    fn can_push_front_push_front_pop_back_pop_back() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            let bn = 73;
            let mut b = LinkedListNode::new(bn);
            assert_eq!(ll.len(), 0);
            ll.push_front(core::ptr::addr_of_mut!(a));
            ll.push_front(core::ptr::addr_of_mut!(b));

            let aa = ll.pop_back().expect("failed to pop_back");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);

            let bb = ll.pop_back().expect("failed to pop_back");
            assert_eq!(bb, core::ptr::addr_of_mut!(b));
            assert_eq!(*(*bb).data(), bn);
        }
    }

    #[test]
    fn can_push_back_push_back_pop_front_pop_front() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            let bn = 73;
            let mut b = LinkedListNode::new(bn);
            assert_eq!(ll.len(), 0);
            ll.push_back(core::ptr::addr_of_mut!(a));
            ll.push_back(core::ptr::addr_of_mut!(b));

            let aa = ll.pop_front().expect("failed to pop_front");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);

            let bb = ll.pop_front().expect("failed to pop_front");
            assert_eq!(bb, core::ptr::addr_of_mut!(b));
            assert_eq!(*(*bb).data(), bn);
        }
    }

    #[test]
    fn can_push_back_push_back_pop_back_pop_back() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let mut a = LinkedListNode::new(an);
            let bn = 73;
            let mut b = LinkedListNode::new(bn);
            assert_eq!(ll.len(), 0);
            ll.push_back(core::ptr::addr_of_mut!(a));
            ll.push_back(core::ptr::addr_of_mut!(b));

            let bb = ll.pop_back().expect("failed to pop_back");
            assert_eq!(bb, core::ptr::addr_of_mut!(b));
            assert_eq!(*(*bb).data(), bn);

            let aa = ll.pop_back().expect("failed to pop_back");
            assert_eq!(aa, core::ptr::addr_of_mut!(a));
            assert_eq!(*(*aa).data(), an);
        }
    }

    #[test]
    fn smoke_test() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);
            let an = 73;
            let bn = 42;
            let mut a = LinkedListNode::new(an);
            let mut b = LinkedListNode::new(bn);
            assert_eq!(ll.len(), 0);
            ll.push_back(core::ptr::addr_of_mut!(a));
            assert_eq!(ll.len(), 1);
            ll.push_back(core::ptr::addr_of_mut!(b));
            assert_eq!(ll.len(), 2);
            assert_eq!(*(*ll.pop_front().expect("pop returned none")).data(), an);
            assert_eq!(ll.len(), 1);
            assert_eq!(*(*ll.pop_front().expect("pop returned none")).data(), bn);
            assert_eq!(ll.len(), 0);
            assert_eq!(ll.pop_front(), None);

            assert_eq!(ll.len(), 0);
            ll.push_front(core::ptr::addr_of_mut!(a));
            assert_eq!(ll.len(), 1);
            ll.push_front(core::ptr::addr_of_mut!(b));
            assert_eq!(ll.len(), 2);
            assert_eq!(*(*ll.pop_back().expect("pop returned none")).data(), an);
            assert_eq!(ll.len(), 1);
            assert_eq!(*(*ll.pop_back().expect("pop returned none")).data(), bn);
            assert_eq!(ll.len(), 0);
            assert_eq!(ll.pop_back(), None);
        }
    }

    #[test]
    fn can_append() {
        let ref1 = [0, 1, 2];
        let ref2 = [3, 4, 5];
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll1 = LinkedList::new(&mut sentinel_ptr);
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll2 = LinkedList::new(&mut sentinel_ptr);

        for i in ref1 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll1.push_back(n) };
        }

        for i in ref2 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll2.push_back(n) };
        }

        unsafe { ll1.append(ll2) };
    }

    #[test]
    fn append_sets_head_and_tail() {
        let ref1 = [0, 1, 2];
        let ref2 = [3, 4, 5];
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll1 = LinkedList::new(&mut sentinel_ptr);
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll2 = LinkedList::new(&mut sentinel_ptr);

        for i in ref1 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll1.push_back(n) };
        }

        for i in ref2 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll2.push_back(n) };
        }

        unsafe { ll1.append(ll2) };

        unsafe {
            let head = (*ll1.sentinel).next();
            assert_eq!(*(*head).data(), 0);
            let tail = (*ll1.sentinel).prev();
            assert_eq!(*(*tail).data(), 5);
        }
    }

    #[test]
    fn append_iter() {
        let ref1 = [0, 1, 2];
        let ref2 = [3, 4, 5];
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll1 = LinkedList::new(&mut sentinel_ptr);
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll2 = LinkedList::new(&mut sentinel_ptr);

        for i in ref1 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll1.push_back(n) };
        }

        for i in ref2 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll2.push_back(n) };
        }

        unsafe { ll1.append(ll2) };

        let ref_iter = ref1.iter().chain(ref2.iter());
        for (ref_i, i_node) in ref_iter.zip(ll1.iter()) {
            assert_eq!(ref_i, i_node.data());
        }
    }

    #[test]
    fn can_prepend() {
        let ref1 = [0, 1, 2];
        let ref2 = [3, 4, 5];
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll1 = LinkedList::new(&mut sentinel_ptr);
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll2 = LinkedList::new(&mut sentinel_ptr);

        for i in ref1 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll2.push_back(n) };
        }

        for i in ref2 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll1.push_back(n) };
        }

        unsafe { ll1.prepend(ll2) };
    }

    #[test]
    fn prepend_sets_head_and_tail() {
        let ref1 = [0, 1, 2];
        let ref2 = [3, 4, 5];
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll1 = LinkedList::new(&mut sentinel_ptr);
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll2 = LinkedList::new(&mut sentinel_ptr);

        for i in ref1 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll2.push_back(n) };
        }

        for i in ref2 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll1.push_back(n) };
        }

        unsafe { ll1.prepend(ll2) };

        unsafe {
            let head = (*ll1.sentinel).next();
            assert_eq!(*(*head).data(), 0);
            let tail = (*ll1.sentinel).prev();
            assert_eq!(*(*tail).data(), 5);
        }
    }

    #[test]
    fn prepend_iter() {
        let ref1 = [0, 1, 2];
        let ref2 = [3, 4, 5];
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll1 = LinkedList::new(&mut sentinel_ptr);
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll2 = LinkedList::new(&mut sentinel_ptr);

        for i in ref1 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll2.push_back(n) };
        }

        for i in ref2 {
            let n = Box::into_raw(Box::new(LinkedListNode::new(i)));
            unsafe { ll1.push_back(n) };
        }

        unsafe { ll1.prepend(ll2) };

        let ref_iter = ref1.iter().chain(ref2.iter());
        for (ref_i, i_node) in ref_iter.zip(ll1.iter()) {
            assert_eq!(ref_i, i_node.data());
        }
    }

    #[test]
    fn can_unlink_self() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);
        let data = [0, 1, 2];
        for i in data.iter() {
            let n = Box::into_raw(Box::new(LinkedListNode::new(*i)));
            unsafe { ll.push_back(n) };
        }

        unsafe {
            let head_ptr = (*ll.sentinel).next();
            let mid_ptr = (*head_ptr).next();
            (*mid_ptr).unlink_self();
        }

        unsafe {
            let head_ptr = (*ll.sentinel).next();
            let tail_ptr = (*ll.sentinel).prev();
            // validate our head and tail are still what we expect
            assert_eq!(*(*head_ptr).data(), 0);
            assert_eq!(*(*tail_ptr).data(), 2);
            // validate our head now points to our tail
            assert_eq!((*head_ptr).next(), tail_ptr);
            // validate our tail now points to our head
            assert_eq!((*tail_ptr).prev(), head_ptr);
        }
    }

    #[test]
    fn can_unlink_through_mut_iter() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);
        let data = [0, 1, 2];

        for i in data.iter() {
            let n = Box::into_raw(Box::new(LinkedListNode::new(*i)));
            unsafe { ll.push_back(n) };
        }

        for n in ll.iter_mut() {
            if *n.data() == 1 {
                n.unlink_self();
            }
        }

        unsafe {
            let head_ptr = (*ll.sentinel).next();
            let tail_ptr = (*ll.sentinel).prev();
            // validate our head and tail are still what we expect
            assert_eq!(*(*head_ptr).data(), 0);
            assert_eq!(*(*tail_ptr).data(), 2);
            // validate our head now points to our tail
            assert_eq!((*head_ptr).next(), tail_ptr);
            // validate our tail now points to our head
            assert_eq!((*tail_ptr).prev(), head_ptr);
        }
    }

    #[test]
    fn peek_next_data_returns_none_if_next_is_sentinel() {
        let mut sentinel = MaybeUninit::uninit();
        LinkedListNode::init_sentinel(&mut sentinel);
        let mut n = LinkedListNode::new(1);
        n.set_next(sentinel.as_mut_ptr());
        assert!(n.peek_next_data().is_none());
    }

    #[test]
    fn peek_next_data_returns_next_if_data() {
        let mut n1 = LinkedListNode::new(1);
        let mut n2 = LinkedListNode::new(2);
        n1.set_next(core::ptr::addr_of_mut!(n2));
        let next = n1.peek_next_data().expect("next should be some");
        assert_eq!(next, n2.data());
    }

    #[test]
    fn peek_prev_data_returns_none_if_next_is_sentinel() {
        let mut sentinel = MaybeUninit::uninit();
        LinkedListNode::init_sentinel(&mut sentinel);
        let mut n = LinkedListNode::new(1);
        n.set_prev(sentinel.as_mut_ptr());
        assert!(n.peek_prev_data().is_none());
    }

    #[test]
    fn peek_prev_data_returns_next_if_data() {
        let mut n1 = LinkedListNode::new(1);
        let mut n2 = LinkedListNode::new(2);
        n1.set_prev(core::ptr::addr_of_mut!(n2));
        let next = n1.peek_prev_data().expect("prev should be some");
        assert_eq!(next, n2.data());
    }
}

#[cfg(test)]
mod iter_test {
    use super::*;

    #[test]
    fn basic_iter_test() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let nums = [73, 42, 114, 901];

            let mut n = LinkedListNode::new(nums[0]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut n = LinkedListNode::new(nums[1]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut n = LinkedListNode::new(nums[2]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut n = LinkedListNode::new(nums[3]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            for (node, num) in ll.iter().zip(nums.iter()) {
                assert_eq!(node.data(), num);
            }
        }
    }

    #[test]
    fn iter_terminates_properly_single_element() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val = 42;
            let mut n = LinkedListNode::new(val);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut iter = ll.iter();
            assert_eq!(&val, iter.next().expect("should produce a value").data());

            for _i in 0..10 {
                assert!(iter.next().is_none());
            }
        }
    }

    #[test]
    fn iter_terminates_properly_multi_element() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let val2 = 73;
            let mut n = LinkedListNode::new(val2);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut iter = ll.iter();
            assert_eq!(&val1, iter.next().expect("should produce a value").data());
            assert_eq!(&val2, iter.next().expect("should produce a value").data());

            for _i in 0..10 {
                assert!(iter.next().is_none());
            }
        }
    }

    #[test]
    fn basic_iter_mut_test() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let nums = [73, 42, 114, 901];

            let mut n = LinkedListNode::new(nums[0]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut n = LinkedListNode::new(nums[1]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut n = LinkedListNode::new(nums[2]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut n = LinkedListNode::new(nums[3]);
            ll.push_back(core::ptr::addr_of_mut!(n));

            for node in ll.iter_mut() {
                *node.data_mut() += 1;
            }

            for (node, num) in ll.iter().zip(nums.iter()) {
                assert_eq!(node.data(), &(*num + 1));
            }
        }
    }

    #[test]
    fn iter_mut_terminates_properly_single_element() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val = 42;
            let mut n = LinkedListNode::new(val);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut iter = ll.iter_mut();
            assert_eq!(&val, iter.next().expect("should produce a value").data());

            for _i in 0..10 {
                assert!(iter.next().is_none());
            }
        }
    }

    #[test]
    fn iter_mut_terminates_properly_multi_element() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let val2 = 73;
            let mut n = LinkedListNode::new(val2);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut iter = ll.iter_mut();
            assert_eq!(&val1, iter.next().expect("should produce a value").data());
            assert_eq!(&val2, iter.next().expect("should produce a value").data());

            for _i in 0..10 {
                assert!(iter.next().is_none());
            }
        }
    }
}

#[cfg(test)]
mod cursor_tests {
    use super::*;

    #[test]
    fn can_create_cursor() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll: LinkedList<u32> = LinkedList::new(&mut sentinel_ptr);
        let _ = ll.cursor();
    }

    #[test]
    fn cursor_on_empty_list_never_returns_data() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll: LinkedList<u32> = LinkedList::new(&mut sentinel_ptr);
        let mut cursor = ll.cursor();
        for _ in 0..100 {
            assert!(cursor.curr_data().is_none());
            cursor.move_next();
        }
        for _ in 0..100 {
            assert!(cursor.curr_data_mut().is_none());
            cursor.move_prev();
        }
    }

    #[test]
    fn cursor_iterates_through_values_in_both_directions() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let val2 = 73;
            let mut n = LinkedListNode::new(val2);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut cursor = ll.cursor();

            // cursors start at the sentinel
            cursor.move_next();

            assert_eq!(*cursor.curr_data().unwrap(), val1);
            cursor.move_next();
            assert_eq!(*cursor.curr_data().unwrap(), val2);
            cursor.move_next();
            assert!(cursor.curr_data().is_none());
            cursor.move_prev();
            assert_eq!(*cursor.curr_data().unwrap(), val2);
            cursor.move_prev();
            assert_eq!(*cursor.curr_data().unwrap(), val1);
            cursor.move_prev();
            assert!(cursor.curr_data().is_none());
        }
    }

    #[test]
    fn cursor_can_mutate_elements() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let val2 = 73;
            let mut n = LinkedListNode::new(val2);
            ll.push_back(core::ptr::addr_of_mut!(n));

            let mut cursor = ll.cursor();

            // cursors start at the sentinel
            cursor.move_next();

            *cursor.curr_data_mut().unwrap() += 1;
            cursor.move_next();
            *cursor.curr_data_mut().unwrap() += 1;

            let mut iter = ll.iter();
            assert_eq!(*iter.next().unwrap().data(), val1 + 1);
            assert_eq!(*iter.next().unwrap().data(), val2 + 1);
            assert!(iter.next().is_none());
        }
    }

    #[test]
    fn cursor_can_remove_elements() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n1 = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n1));

            let val2 = 73;
            let mut n2 = LinkedListNode::new(val2);
            ll.push_back(core::ptr::addr_of_mut!(n2));

            let val3 = 119;
            let mut n3 = LinkedListNode::new(val3);
            ll.push_back(core::ptr::addr_of_mut!(n3));

            let prev_len = ll.len();

            let mut cursor = ll.cursor();

            // cursors start at the sentinel
            cursor.move_next();

            cursor.move_next();
            assert_eq!(*cursor.curr_data().unwrap(), val2);
            let middle_node = cursor
                .remove_curr()
                .expect("shouldn't have been on sentinel");
            // validate we get the right node back
            assert_eq!(middle_node as usize, core::ptr::addr_of_mut!(n2) as usize);
            assert_eq!(*(*middle_node).data(), val2);
            // validate the cursor moved forward
            assert_eq!(*cursor.curr_data().unwrap(), val3);
            // validate the list's length decreased by one
            assert_eq!(prev_len - 1, ll.len());
        }
    }

    #[test]
    fn trying_to_remove_element_sentinel_does_nothing() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n1 = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n1));

            let val2 = 73;
            let mut n2 = LinkedListNode::new(val2);
            ll.push_back(core::ptr::addr_of_mut!(n2));

            let prev_len = ll.len();

            // cursors start on the sentinel
            let mut cursor = ll.cursor();
            assert!(cursor.curr_data().is_none());

            // validate that trying to remove the sentinel returns none
            assert!(cursor.remove_curr().is_none());

            // validate our cursor hasn't moved
            assert!(cursor.curr_data().is_none());

            // validate the list's length hasn't changed
            assert_eq!(prev_len, ll.len());
        }
    }

    #[test]
    fn cursor_can_insert_before_curr_in_empty_list() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);

        let mut cursor = ll.cursor();

        let val1 = 42;
        let mut n1 = LinkedListNode::new(val1);

        // validate we're in the expected spot
        assert!(cursor.curr_data().is_none());

        unsafe { cursor.insert_before_curr(core::ptr::addr_of_mut!(n1)) };

        // validate we're still on the sentinel node
        assert!(cursor.curr_data().is_none());

        cursor.move_prev();

        // validate we're on the newly inserted node
        assert_eq!(*cursor.curr_data().unwrap(), val1);

        // validate we're properly linked back to the sentinel
        cursor.move_prev();
        assert!(cursor.curr_data().is_none());

        // validate we can move forward back to our new node
        cursor.move_next();
        assert_eq!(*cursor.curr_data().unwrap(), val1);

        // validate we can move forward to the sentinel
        cursor.move_next();
        assert!(cursor.curr_data().is_none());
    }

    #[test]
    fn cursor_can_insert_before_curr_in_populated_list() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n1 = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n1));

            let val2 = 42;
            let mut n2 = LinkedListNode::new(val2);
            ll.push_back(core::ptr::addr_of_mut!(n2));

            let mut cursor = ll.cursor();

            // cursors start at the sentinel
            cursor.move_next();

            let val3 = 73;
            let mut n3 = LinkedListNode::new(val3);

            // validate we're in the expected spot
            assert_eq!(*cursor.curr_data().unwrap(), val1);

            cursor.insert_before_curr(core::ptr::addr_of_mut!(n3));

            // validate we're still on the first node
            assert_eq!(*cursor.curr_data().unwrap(), val1);

            cursor.move_prev();

            // validate we're on the newly inserted node
            assert_eq!(*cursor.curr_data().unwrap(), val3);

            // validate we're properly linked to the sentinel
            cursor.move_prev();
            assert!(cursor.curr_data().is_none());

            // validate we can move forward back to our new node
            cursor.move_next();
            assert_eq!(*cursor.curr_data().unwrap(), val3);

            // validate we can move forward to the original node
            cursor.move_next();
            assert_eq!(*cursor.curr_data().unwrap(), val1);

            let head = ll.head().unwrap();
            assert_eq!(*(*head).data(), val3);

            let mut iter = ll.iter();
            assert_eq!(*iter.next().unwrap().data(), val3);
            assert_eq!(*iter.next().unwrap().data(), val1);
            assert_eq!(*iter.next().unwrap().data(), val2);

            // TODO [matthew-russo] this discovers UB under stacked borrows rules
            // but I haven't figured out a way to make the linked list code sound.
            // given this is on the sentinel, there is some special pointer interactions
            // happening there when inserting nodes via the cursor
            // assert!(iter.next().is_none());
        }
    }

    #[test]
    fn cursor_can_insert_after_curr_in_empty_list() {
        let mut sentinel_ptr = MaybeUninit::uninit();
        let mut ll = LinkedList::new(&mut sentinel_ptr);

        let mut cursor = ll.cursor();

        let val1 = 42;
        let mut n1 = LinkedListNode::new(val1);

        // validate we're in the expected spot
        assert!(cursor.curr_data().is_none());

        unsafe { cursor.insert_after_curr(core::ptr::addr_of_mut!(n1)) };

        // validate we're still on the sentinel node
        assert!(cursor.curr_data().is_none());

        cursor.move_next();

        // validate we're on the newly inserted node
        assert_eq!(*cursor.curr_data().unwrap(), val1);

        // validate we're properly linked back to the sentinel
        cursor.move_next();
        assert!(cursor.curr_data().is_none());

        // validate we can move forward back to our new node
        cursor.move_prev();
        assert_eq!(*cursor.curr_data().unwrap(), val1);

        // validate we can move forward to the sentinel
        cursor.move_prev();
        assert!(cursor.curr_data().is_none());
    }

    #[test]
    fn cursor_can_insert_after_curr_in_populated_list() {
        unsafe {
            let mut sentinel_ptr = MaybeUninit::uninit();
            let mut ll = LinkedList::new(&mut sentinel_ptr);

            let val1 = 42;
            let mut n1 = LinkedListNode::new(val1);
            ll.push_back(core::ptr::addr_of_mut!(n1));

            let mut cursor = ll.cursor();

            // cursors start at the sentinel
            cursor.move_next();

            let val2 = 73;
            let mut n2 = LinkedListNode::new(val2);

            // validate we're in the expected spot
            assert_eq!(*cursor.curr_data().unwrap(), val1);

            cursor.insert_after_curr(core::ptr::addr_of_mut!(n2));

            // validate we're still on the first node
            assert_eq!(*cursor.curr_data().unwrap(), val1);

            cursor.move_next();

            // validate we're on the newly inserted node
            assert_eq!(*cursor.curr_data().unwrap(), val2);

            // validate we're properly linked to the sentinel
            cursor.move_next();
            assert!(cursor.curr_data().is_none());

            // validate we can move backward back to our new node
            cursor.move_prev();
            assert_eq!(*cursor.curr_data().unwrap(), val2);

            // validate we can move backward to the original node
            cursor.move_prev();
            assert_eq!(*cursor.curr_data().unwrap(), val1);

            let mut iter = ll.iter();
            assert_eq!(*iter.next().unwrap().data(), val1);
            assert_eq!(*iter.next().unwrap().data(), val2);
            assert!(iter.next().is_none());
        }
    }
}

// proptest doesn't run under miri with default config
#[cfg(all(not(miri), test))]
mod proptests {
    use std::collections::LinkedList as StdLinkedList;

    use proptest::prelude::*;
    use proptest::test_runner::Config;
    use proptest_state_machine::{ReferenceStateMachine, StateMachineTest};

    use super::*;

    // Setup the state machine test using the `prop_state_machine!` macro
    proptest_state_machine::prop_state_machine! {
        #![proptest_config(Config {
            // Turn failure persistence off for demonstration. This means that no
            // regression file will be captured.
            failure_persistence: None,
            // Enable verbose mode to make the state machine test print the
            // transitions for each case.
            verbose: 1,
            .. Config::default()
        })]

        #[test]
        fn linked_list_state_machine_test(
            // This is a macro's keyword - only `sequential` is currently supported.
            sequential
            // The number of transitions to be generated for each case. This can
            // be a single numerical value or a range as in here.
            100..500
            // Macro's boilerplate to separate the following identifier.
            =>
            // The name of the type that implements `StateMachineTest`.
            LinkedList<u32>
        );
    }

    /// The possible transitions of the state machine.
    #[derive(Clone, Debug)]
    pub enum Transition {
        PushFront(u32),
        PopFront,
        PushBack(u32),
        PopBack,
    }

    pub struct LinkedListStateMachine;

    // Implementation of the reference state machine that drives the test. That is,
    // it's used to generate a sequence of transitions the `StateMachineTest`.
    impl ReferenceStateMachine for LinkedListStateMachine {
        type State = StdLinkedList<u32>;
        type Transition = Transition;

        fn init_state() -> BoxedStrategy<Self::State> {
            Just(StdLinkedList::new()).boxed()
        }

        fn transitions(_state: &Self::State) -> BoxedStrategy<Self::Transition> {
            // Using the regular proptest constructs here, the transitions can be
            // given different weights.
            prop_oneof![
                1 => Just(Transition::PopFront),
                2 => (any::<u32>()).prop_map(Transition::PushFront),
                1 => Just(Transition::PopBack),
                2 => (any::<u32>()).prop_map(Transition::PushBack),            ]
            .boxed()
        }

        fn apply(mut state: Self::State, transition: &Self::Transition) -> Self::State {
            match transition {
                Transition::PopFront => {
                    state.pop_front();
                }
                Transition::PushFront(value) => state.push_front(*value),
                Transition::PopBack => {
                    state.pop_back();
                }
                Transition::PushBack(value) => state.push_back(*value),
            }
            state
        }
    }

    impl StateMachineTest for LinkedList<u32> {
        type SystemUnderTest = Self;
        type Reference = LinkedListStateMachine;

        fn init_test(
            _ref_state: &<Self::Reference as ReferenceStateMachine>::State,
        ) -> Self::SystemUnderTest {
            let sentinel = Box::leak(Box::new(MaybeUninit::uninit()));
            Self::new(sentinel)
        }

        fn apply(
            mut state: Self::SystemUnderTest,
            _ref_state: &<Self::Reference as ReferenceStateMachine>::State,
            transition: Transition,
        ) -> Self::SystemUnderTest {
            match transition {
                Transition::PushFront(value) => {
                    let lln = LinkedListNode::new(value);
                    unsafe { state.push_front(Box::into_raw(Box::new(lln))) };
                }
                Transition::PopFront => {
                    if let Some(lln_ptr) = unsafe { state.pop_front() } {
                        let _ = unsafe { Box::from_raw(lln_ptr) };
                    }
                }
                Transition::PushBack(value) => {
                    let lln = LinkedListNode::new(value);
                    unsafe { state.push_back(Box::into_raw(Box::new(lln))) };
                }
                Transition::PopBack => {
                    if let Some(lln_ptr) = unsafe { state.pop_back() } {
                        let _ = unsafe { Box::from_raw(lln_ptr) };
                    }
                }
            }
            state
        }

        fn check_invariants(
            state: &Self::SystemUnderTest,
            ref_state: &<Self::Reference as ReferenceStateMachine>::State,
        ) {
            assert_eq!(state.len(), ref_state.len());

            for (ll_node, ref_value) in state.iter().zip(ref_state.iter()) {
                assert_eq!(ll_node.data(), ref_value);
            }
        }
    }
}

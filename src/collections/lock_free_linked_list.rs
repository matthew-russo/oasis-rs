use crate::sync::tagged_ptr::TaggedPtr;

/// a node in the lock-free linked list
pub struct Node<T> {
    /// the underlying data pointed to by this node
    data: *mut T,
    /// the previous node in the list, represented as a TaggedPtr which stores
    /// whether the node is logically removed from the list
    prev: TaggedPtr<Node<T>>,
    /// the next node in the list, represented as a TaggedPtr which stores
    /// whether the node is logically removed from the list
    next: TaggedPtr<Node<T>>,
}

impl<T> Node<T> {
    /// construct a new node with the provided data, with its previous and next
    /// pointers initialized to the null pointer
    pub fn new(data: *mut T) -> Self {
        Self {
            data,
            prev: TaggedPtr::new(core::ptr::null_mut()),
            next: TaggedPtr::new(core::ptr::null_mut()),
        }
    }

    fn prev(&self) -> TaggedPtr<Node<T>> {
        self.prev.copy_ptr()
    }

    fn next(&self) -> TaggedPtr<Node<T>> {
        self.next.copy_ptr()
    }
}

impl<T> core::fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Node")
            .field("prev", &self.prev)
            .field("self", &core::ptr::addr_of!(*self))
            .field("data", &self.data)
            .field("next", &self.next)
            .finish()
    }
}

/// an implementation of Sundell and Tsigas' lock-free doubly-linked list
///
/// https://arxiv.org/abs/cs/0408016
/// https://arxiv.org/pdf/cs/0408016
#[derive(Clone)]
pub struct LockFreeLinkedList<T> {
    sentinel_head: TaggedPtr<Node<T>>,
    sentinel_tail: TaggedPtr<Node<T>>,
}

impl<T: 'static> LockFreeLinkedList<T> {
    /// create a new linked list
    pub fn new() -> Self {
        let head = Node::new(core::ptr::null_mut());
        let head = TaggedPtr::new(Box::into_raw(Box::new(head)));

        let tail = Node::new(core::ptr::null_mut());
        let tail = TaggedPtr::new(Box::into_raw(Box::new(tail)));

        head.deref_untagged().next.set_ptr(tail.get_ptr());
        tail.deref_untagged().prev.set_ptr(head.get_ptr());

        Self {
            sentinel_head: head,
            sentinel_tail: tail,
        }
    }

    /// push a node to the front of the list
    pub fn push_front(&self, node: &'static mut Node<T>) {
        // (1): INIT
        // initialize the Node
        let node = TaggedPtr::new(core::ptr::addr_of_mut!(*node));
        let prev = self.sentinel_head.clone();
        let mut current_head = prev.deref_untagged().next();

        loop {
            // if a concurrent op already won, try again
            if prev.deref_untagged().next().get_ptr() != current_head.untagged() {
                current_head = prev.deref_untagged().next();
                continue;
            }

            // prep the node for insertion in between our sentinel head and the current head
            node.deref_untagged().prev.set_ptr(prev.untagged());
            node.deref_untagged().next.set_ptr(current_head.untagged());

            // (2): LOGICALLY INSERT
            // update the sentinel head's next pointer to point to our new node
            if prev
                .deref_untagged()
                .next
                .cas(current_head.untagged(), node.untagged())
            {
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }

        // fixup current_head's prev pointer
        self.push_common(node, current_head);
    }

    /// push a node to the back of the list
    pub fn push_back(&self, node: &'static mut Node<T>) {
        // (1): INIT
        // initialize the node
        let node = TaggedPtr::new(core::ptr::addr_of_mut!(*node));
        let next = self.sentinel_tail.clone();
        let mut current_tail = next.deref_untagged().prev();

        loop {
            // if a concurrent op already won, help cleanup and try again
            if current_tail.deref_untagged().next.get_ptr() != self.sentinel_tail.untagged() {
                current_tail = self.help_insert(current_tail, self.sentinel_tail.clone());
                continue;
            }

            // prep the node for insertion in between the current tail and our sentinel tail
            node.deref_untagged().prev.set_ptr(current_tail.untagged());
            node.deref_untagged().next.set_ptr(self.sentinel_tail.untagged());

            // (2): LOGICALLY INSERT
            // update the current tail's next pointer to point to our node
            if current_tail
                .deref_untagged()
                .next
                .cas(self.sentinel_tail.untagged(), node.untagged())
            {
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }

        // fixup sentinel_tails's prev pointer
        self.push_common(node, self.sentinel_tail.clone());
    }

    /// pop a node from the front of the list, or None if the list is empty
    pub fn pop_front(&self) -> Option<&'static mut Node<T>> {
        let mut current_head: TaggedPtr<Node<T>>;
        loop {
            current_head = self.sentinel_head.deref_untagged().next();

            // if the list is empty, return None
            if current_head.get_ptr() == self.sentinel_tail.get_ptr() {
                return None;
            }

            // get the node that will be the new head. if its tagged, help clean up and try
            // again
            let new_head = current_head.deref_untagged().next();
            if new_head.is_tagged() {
                self.help_delete(current_head);
                continue;
            }

            // (4): LOGICALLY REMOVE
            // update the current head's next pointer to be tagged, logically removing it
            // from the list
            if current_head
                .deref_untagged()
                .next
                .cas(new_head.get_ptr(), new_head.tagged())
            {
                self.help_delete(current_head.clone());
                let next = current_head.deref_untagged().next();
                let _prev = self.help_insert(self.sentinel_head.clone(), next);
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }

        self.remove_cross_reference(&current_head);
        Some(current_head.deref_untagged_mut())
    }

    /// pop a node from the back of the list, or None if the list is empty
    pub fn pop_back(&self) -> Option<&'static mut Node<T>> {
        let mut current_tail = self.sentinel_tail.deref_untagged().prev();

        loop {
            // if the current tail's next ptr is tagged or doesn't point to the sentinel
            // tail, help clean up and try again
            if current_tail.deref_untagged().next.get_ptr() != self.sentinel_tail.untagged() {
                current_tail = self.help_insert(current_tail, self.sentinel_tail.clone());
                continue;
            }

            // if the list is empty return none
            if current_tail.get_ptr() == self.sentinel_head.get_ptr() {
                return None;
            }

            // (4): LOGICALLY REMOVE
            // update the current tails next pointer to be tagged, logically removing it
            // from the list
            if current_tail
                .deref_untagged()
                .next
                .cas(self.sentinel_tail.untagged(), self.sentinel_tail.tagged())
            {
                // clean up the now-deleted node
                self.help_delete(current_tail.clone());

                // fix up pointeres for our new tail
                let new_tail = current_tail.deref_untagged().prev();
                self.help_insert(new_tail, self.sentinel_tail.clone());
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }

        self.remove_cross_reference(&current_tail);
        Some(current_tail.deref_untagged_mut())
    }

    /// fixup newly inserted node's next node to point backwards to node
    fn push_common(&self, node: TaggedPtr<Node<T>>, next: TaggedPtr<Node<T>>) {
        loop {
            let next_prev = next.deref_untagged().prev();

            // if a concurrent op is already mutating this data, bail out and let them clean
            // up
            if next_prev.is_tagged() || node.deref_untagged().next.get_ptr() != next.untagged() {
                break;
            }

            // (3): FINALIZE INSERT
            // update the next node's previous ptr to point ot our newly inserted node
            if next.deref_untagged().prev.cas(next_prev.get_ptr(), node.untagged()) {
                if node.deref_untagged().prev.is_tagged() {
                    self.help_insert(node, next);
                }
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }
    }

    /// mark the provided node's previous node as logically removed
    fn mark_prev(&self, node: &TaggedPtr<Node<T>>) {
        loop {
            let prev = node.deref_untagged().prev();
            if prev.is_tagged() || node.deref_untagged().prev.cas(prev.get_ptr(), prev.tagged()) {
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }
    }

    fn remove_cross_reference(&self, node: &TaggedPtr<Node<T>>) {
        loop {
            let prev = node.deref_untagged().prev();

            if prev.deref_untagged().prev.is_tagged() {
                node.deref_untagged().prev.set_ptr(prev.deref_untagged().prev.tagged());
                continue;
            }

            let next = node.deref_untagged().next();

            if next.deref_untagged().prev.is_tagged() {
                node.deref_untagged().next.set_ptr(next.deref_untagged().next.tagged());
                continue;
            }

            break;
        }
    }

    fn help_insert(
        &self,
        mut prev: TaggedPtr<Node<T>>,
        node: TaggedPtr<Node<T>>,
    ) -> TaggedPtr<Node<T>> {
        let mut last: Option<TaggedPtr<Node<T>>> = None;

        loop {
            // get the next node from prev
            let prev_next = prev.deref_untagged().next();
            if prev_next.get_ptr().is_null() {
                if let Some(last_node) = last.take() {
                    self.mark_prev(&prev);
                    let next_2 = prev.deref_untagged().next();
                    last_node
                        .deref_untagged()
                        .next
                        .cas(prev.untagged(), next_2.untagged());
                    prev = last_node;
                    last = None;
                } else {
                    prev = prev.deref_untagged().prev();
                }

                continue;
            }

            let node_prev = node.deref_untagged().prev();
            if node_prev.is_tagged() {
                break;
            }

            // if the prev node isn't pointing to node, keep traversing
            if prev_next.get_ptr() != node.untagged() {
                last = Some(prev);
                prev = prev_next;
                continue;
            }

            if node_prev.untagged() == prev.get_ptr() {
                break;
            }

            if node.deref_untagged().prev.cas(node_prev.get_ptr(), prev.untagged()) &&
                !prev.deref_untagged().prev.is_tagged()
            {
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }

        prev
    }

    fn help_delete(&self, node: TaggedPtr<Node<T>>) {
        self.mark_prev(&node);

        let mut last: Option<TaggedPtr<Node<T>>> = None;
        let mut prev = node.deref_untagged().prev();
        let mut next = node.deref_untagged().next();

        loop {
            if prev.get_ptr() == next.get_ptr() {
                break;
            }

            // if the next node's next ptr is already tagged, mark its prev ptr and continue
            // traversing the list
            if next.deref_untagged().next.is_tagged() {
                self.mark_prev(&next);
                next = next.deref_untagged().next();
                continue;
            }

            let prev_next = prev.deref_untagged().next();
            if prev_next.get_ptr().is_null() {
                if let Some(last_node) = last.take() {
                    self.mark_prev(&prev);
                    let prev_next_2 = prev.deref_untagged().next();
                    if !last_node
                        .deref_untagged()
                        .next
                        .cas(prev.untagged(), prev_next_2.untagged())
                    {
                        prev = last_node;
                        last = None;
                    }
                } else {
                    prev = prev.deref_untagged().prev();
                }

                continue;
            }

            // if the previous nodes next ptr doesn't point to the current node, ???????
            if prev_next.get_ptr() != node.get_ptr() {
                last = Some(prev);
                prev = prev_next;
                continue;
            }

            // try to update the previou node's next ptr to point to the current node's next
            // ptr
            if prev.deref_untagged().next.cas(node.untagged(), next.untagged()) {
                break;
            }
            #[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
            loom::sync::atomic::spin_loop_hint();
        }
    }
}

impl<T: 'static> Default for LockFreeLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static> LockFreeLinkedList<T> {
    #[allow(dead_code)]
    fn pretty_print(&self) {
        println!("\n\nLockFreeLinkedList: ");
        let mut curr = &self.sentinel_head;

        while !curr.get_ptr().is_null() {
            let c = curr.deref_untagged();
            println!(
                "\n<-- {:?} -- ( self: {:p} data: {:p} ) -- {:?} -->",
                c.prev,
                core::ptr::addr_of!(*c),
                c.data,
                c.next,
            );
            curr = &c.next;
        }
    }
}

#[cfg(all(test, not(feature = "loom")))]
mod test {
    use super::*;

    #[test]
    fn can_push_front() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_front(f);
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([4, 5, 6, 7])))));
        ll.push_front(f);
        ll.pretty_print();
    }

    #[test]
    fn can_push_back() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_back(f);
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([4, 5, 6, 7])))));
        ll.push_back(f);
        ll.pretty_print();
    }

    #[test]
    fn can_pop_front() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_front(f);
        ll.pretty_print();

        let f1 = ll.pop_front().unwrap();
        assert_eq!(unsafe { &*f1.data }, &[0, 1, 2, 3]);

        ll.pretty_print();
    }

    #[test]
    fn can_pop_back() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_back(f);
        ll.pretty_print();

        let f1 = ll.pop_back().unwrap();
        assert_eq!(unsafe { &*f1.data }, &[0, 1, 2, 3]);

        ll.pretty_print();
    }

    #[test]
    fn push_front_properly_sets_next_and_prev_of_sentinels() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f_ptr = Box::into_raw(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_front(unsafe { &mut *f_ptr });
        ll.pretty_print();

        let head = ll.sentinel_head.clone();
        let tail = ll.sentinel_tail.clone();

        unsafe {
            // check forward references
            assert_eq!(head.deref_untagged().next.get_ptr(), core::ptr::addr_of_mut!(*f_ptr));
            assert_eq!((*f_ptr).next.get_ptr(), tail.get_ptr());

            // check backward references
            assert_eq!(tail.deref_untagged().prev.get_ptr(), core::ptr::addr_of_mut!(*f_ptr));
            assert_eq!((*f_ptr).prev.get_ptr(), head.get_ptr());
        }
    }

    #[test]
    fn push_back_properly_sets_next_and_prev_of_sentinels() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f_ptr = Box::into_raw(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_back(unsafe { &mut *f_ptr });
        ll.pretty_print();

        let head = ll.sentinel_head.clone();
        let tail = ll.sentinel_tail.clone();

        unsafe {
            // check forward references
            assert_eq!(head.deref_untagged().next.get_ptr(), core::ptr::addr_of_mut!(*f_ptr));
            assert_eq!((*f_ptr).next.get_ptr(), tail.get_ptr());

            // check backward references
            assert_eq!(tail.deref_untagged().prev.get_ptr(), core::ptr::addr_of_mut!(*f_ptr));
            assert_eq!((*f_ptr).prev.get_ptr(), head.get_ptr());
        }
    }

    #[test]
    fn pop_front_properly_cleans_up_next_and_prev_of_sentinels() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_front(f);
        ll.pop_front().expect("failed to pop front");
        ll.pretty_print();

        let head = ll.sentinel_head.clone();
        let tail = ll.sentinel_tail.clone();

        unsafe {
            assert_eq!(head.deref_untagged().next.get_ptr(), tail.get_ptr());
            assert_eq!(tail.deref_untagged().prev.get_ptr(), head.get_ptr());
        }
    }

    #[test]
    fn pop_back_properly_cleans_up_next_and_prev_of_sentinels() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_back(f);
        ll.pop_back().expect("failed to pop front");
        ll.pretty_print();

        let head = ll.sentinel_head.clone();
        let tail = ll.sentinel_tail.clone();

        unsafe {
            assert_eq!(head.deref_untagged().next.get_ptr(), tail.get_ptr());
            assert_eq!(tail.deref_untagged().prev.get_ptr(), head.get_ptr());
        }
    }

    #[test]
    fn smoke_test() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_back(f);
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([4, 5, 6, 7])))));
        ll.push_back(f);
        ll.pretty_print();

        let f1 = ll.pop_front().unwrap();
        assert_eq!(unsafe { &*f1.data }, &[0, 1, 2, 3]);

        ll.pretty_print();
    }

    #[test]
    fn smoke_test_2() {
        let ll = LockFreeLinkedList::new();
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([0, 1, 2, 3])))));
        ll.push_back(f);
        ll.pretty_print();

        let f = Box::leak(Box::new(Node::new(Box::into_raw(Box::new([4, 5, 6, 7])))));
        ll.push_back(f);
        ll.pretty_print();

        let f1 = ll.pop_back().unwrap();
        assert_eq!(unsafe { &*f1.data }, &[4, 5, 6, 7]);

        ll.pretty_print();
    }
}

#[cfg(all(not(feature = "no-std"), all(test, feature = "loom")))]
mod loom_tests {
    use proptest::collection::vec;
    use proptest::prelude::*;
    use proptest_derive::Arbitrary;

    use super::*;

    #[derive(Arbitrary, Clone, Copy, Debug)]
    enum Operation {
        PushFront,
        PushBack,
        PopFront,
        PopBack,
    }

    impl Operation {
        fn execute<T: 'static>(&self, ll: &LockFreeLinkedList<T>, supplier: impl FnOnce() -> T) {
            match self {
                Self::PushFront => {
                    let val = supplier();
                    let val = Box::into_raw(Box::new(val));
                    let node = Box::leak(Box::new(Node::new(val)));
                    ll.push_front(node);
                }
                Self::PushBack => {
                    let val = supplier();
                    let val = Box::into_raw(Box::new(val));
                    let node = Box::leak(Box::new(Node::new(val)));
                    ll.push_back(node);
                }
                Self::PopFront => {
                    ll.pop_front();
                }
                Self::PopBack => {
                    ll.pop_back();
                }
            }
        }
    }

    #[derive(Debug)]
    enum Invariant {
        SentinelHeadExists,
        SentinelTailExists,
        CanTraverseLeftToRight,
        CanTraverseRightToLeft,
        CanDerefEachNonSentinelNode,
    }

    impl Invariant {
        fn validate<T: 'static + PartialEq>(&self, ll: &LockFreeLinkedList<T>, data: &T) {
            match self {
                Self::SentinelHeadExists => Self::validate_sentinel_head_exists(ll),
                Self::SentinelTailExists => Self::validate_sentinel_tail_exists(ll),
                Self::CanTraverseLeftToRight => Self::validate_can_traverse_left_to_right(ll),
                Self::CanTraverseRightToLeft => Self::validate_can_traverse_right_to_left(ll),
                Self::CanDerefEachNonSentinelNode => {
                    Self::validate_can_deref_data_of_each_non_sentinel_node(ll, data)
                }
            }
        }

        fn validate_sentinel_head_exists<T: 'static>(ll: &LockFreeLinkedList<T>) {
            unsafe {
                ll.sentinel_head.deref_untagged();
            }
        }

        fn validate_sentinel_tail_exists<T: 'static>(ll: &LockFreeLinkedList<T>) {
            unsafe {
                ll.sentinel_tail.deref_untagged();
            }
        }

        fn validate_can_traverse_left_to_right<T: 'static>(ll: &LockFreeLinkedList<T>) {
            unsafe {
                let mut curr = ll.sentinel_head.deref_untagged().next();
                while curr.untagged() != ll.sentinel_tail.untagged() {
                    curr = curr.deref_untagged().next()
                }
            }
        }

        fn validate_can_traverse_right_to_left<T: 'static>(ll: &LockFreeLinkedList<T>) {
            unsafe {
                let mut curr = ll.sentinel_tail.deref_untagged().prev();
                while curr.untagged() != ll.sentinel_head.untagged() {
                    curr = curr.deref_untagged().prev();
                }
            }
        }

        fn validate_can_deref_data_of_each_non_sentinel_node<T: 'static + PartialEq>(
            ll: &LockFreeLinkedList<T>,
            data: &T,
        ) {
            unsafe {
                let mut curr = ll.sentinel_head.deref_untagged().next();
                while curr.get_ptr() != ll.sentinel_tail.get_ptr() {
                    // validate that the pointer is good to go
                    assert!(*curr.deref_untagged().data == *data, "data doesn't match");
                    curr = curr.deref_untagged().next()
                }
            }
        }
    }

    const ALL_INVARIANTS: [Invariant; 5] = [
        Invariant::SentinelHeadExists,
        Invariant::SentinelTailExists,
        Invariant::CanTraverseLeftToRight,
        Invariant::CanTraverseRightToLeft,
        Invariant::CanDerefEachNonSentinelNode,
    ];

    fn check_all_invariants<T: 'static + PartialEq>(ll: LockFreeLinkedList<T>, data: &T) {
        ALL_INVARIANTS.iter().for_each(|i| {
            println!("Checking invariant: {:?} against LockFreeLinkedList", i,);
            // ll.pretty_print();
            i.validate(&ll, &data);
        })
    }

    proptest! {
        #[test]
        fn longform(ops in vec(any::<Operation>(), 2)) {
            let mut model = loom::model::Builder::new();
            model.max_branches = 100_000;
            model.check(move || {
                println!("Executing {} operations against LockFreeLinkedList\n\t{:?}", ops.len(), ops);

                let ll = LockFreeLinkedList::new();

                let data = [4, 5, 6, 7];

                let mut jhs = Vec::with_capacity(ops.len());
                for op in ops.clone().into_iter() {
                    let ll = ll.clone();
                    let data = data.clone();
                    let jh = loom::thread::spawn(move || {
                        let ll = ll;
                        op.execute(&ll, || data);
                    });
                    jhs.push(jh);
                }
                for jh in jhs {
                    jh.join().expect("failed to join loom thread");
                }

                check_all_invariants(ll, &data);
                println!("Successfully validated {} operations against LockFreeLinkedList against all possible memory orderings!\n\t{:?}", ops.len(), ops);
            });
        }
    }

    #[test]
    fn repro_one() {
        loom::model(move || {
            let ops = [
                Operation::PushFront,
                Operation::PushBack,
                Operation::PopFront,
            ];
            println!(
                "Executing {} operations against LockFreeLinkedList\n\t{:?}",
                ops.len(),
                ops
            );

            let ll = LockFreeLinkedList::new();

            let data = [4, 5, 6, 7];

            for op in ops.iter() {
                println!("Executing op: {:?}", op);
                op.execute(&ll, || data.clone());
            }

            println!("Successfully executed all ops");

            check_all_invariants(ll, &data);
        });
    }

    #[test]
    fn repro_two() {
        loom::model(move || {
            let ops = [Operation::PopFront, Operation::PopFront, Operation::PopBack];
            println!(
                "Executing {} operations against LockFreeLinkedList\n\t{:?}",
                ops.len(),
                ops
            );

            let ll = LockFreeLinkedList::new();

            let data = [4, 5, 6, 7];

            for op in ops.iter() {
                println!("Executing op: {:?}", op);
                op.execute(&ll, || data.clone());
            }

            println!("Successfully executed all ops");

            check_all_invariants(ll, &data);
        });
    }
}

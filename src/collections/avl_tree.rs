#[cfg(feature = "no-std")]
use alloc::boxed::Box;
#[cfg(not(feature = "no-std"))]
use std::boxed::Box;

pub struct AvlTreeNode<T: Ord> {
    balance_factor: i8,
    data: T,
    parent: *mut AvlTreeNode<T>,
    left: *mut AvlTreeNode<T>,
    right: *mut AvlTreeNode<T>,
}

impl<T: Ord> AvlTreeNode<T> {
    fn new(data: T) -> Self {
        Self {
            balance_factor: 0,
            data,
            parent: core::ptr::null_mut(),
            left: core::ptr::null_mut(),
            right: core::ptr::null_mut(),
        }
    }

    fn balance_factor(&self) -> i8 {
        self.balance_factor
    }

    fn set_balance_factor(&mut self, bf: i8) {
        self.balance_factor = bf;
    }

    fn parent(&mut self) -> *mut AvlTreeNode<T> {
        self.parent
    }

    fn set_parent(&mut self, parent: *mut AvlTreeNode<T>) {
        self.parent = parent;
    }

    fn left_child(&mut self) -> *mut AvlTreeNode<T> {
        self.left
    }

    fn set_left_child(&mut self, left: *mut AvlTreeNode<T>) {
        unsafe { (*left).parent = core::ptr::addr_of_mut!(*self) };
        self.left = left;
    }

    fn right_child(&mut self) -> *mut AvlTreeNode<T> {
        self.right
    }

    fn set_right_child(&mut self, right: *mut AvlTreeNode<T>) {
        unsafe { (*right).parent = core::ptr::addr_of_mut!(*self) };
        self.right = right;
    }

    fn subtree_maximum(&mut self) -> *mut AvlTreeNode<T> {
        let mut curr = core::ptr::addr_of_mut!(*self);
        assert!(!curr.is_null());

        while unsafe { !(*curr).right.is_null() } {
            curr = unsafe { (*curr).right };
        }

        curr
    }

    fn subtree_minimum(&mut self) -> *mut AvlTreeNode<T> {
        let mut curr = core::ptr::addr_of_mut!(*self);
        assert!(!curr.is_null());

        while unsafe { !(*curr).left.is_null() } {
            curr = unsafe { (*curr).left };
        }

        curr
    }

    fn successor(&mut self) -> *mut AvlTreeNode<T> {
        let mut curr = core::ptr::addr_of_mut!(*self);
        assert!(!curr.is_null());

        if unsafe { !(*curr).right.is_null() } {
            return unsafe { (*(*curr).right).subtree_minimum() };
        }

        let mut parent = unsafe { (*curr).parent };
        while !parent.is_null() && curr == unsafe { (*parent).right } {
            curr = parent;
            parent = unsafe { (*parent).parent };
        }

        parent
    }

    fn predecessor(&mut self) -> *mut AvlTreeNode<T> {
        let mut curr = core::ptr::addr_of_mut!(*self);
        assert!(!curr.is_null());

        if unsafe { !(*curr).left.is_null() } {
            return unsafe { (*(*curr).left).subtree_maximum() };
        }

        let mut parent = unsafe { (*curr).parent };
        while !parent.is_null() && curr == unsafe { (*parent).left } {
            curr = parent;
            parent = unsafe { (*parent).parent };
        }

        parent
    }
}

fn rotate_left<T: Ord>(
    curr_root: *mut AvlTreeNode<T>,
    heavy_right_child: *mut AvlTreeNode<T>,
) -> *mut AvlTreeNode<T> {
    // Validate the caller hasn't goofed
    assert!(!curr_root.is_null());
    assert!(!heavy_right_child.is_null());
    assert_eq!(unsafe { (*curr_root).right_child() }, heavy_right_child);
    assert_eq!(unsafe { (*heavy_right_child).parent() }, curr_root);

    let curr_root = unsafe { &mut *curr_root };
    let heavy_right_child = unsafe { &mut *heavy_right_child };

    let right_left_child = heavy_right_child.left_child();

    curr_root.set_right_child(right_left_child);
    if !right_left_child.is_null() {
        unsafe { (*right_left_child).set_parent(curr_root) };
    }

    heavy_right_child.set_left_child(curr_root);
    heavy_right_child.set_parent(curr_root.parent);
    curr_root.set_parent(heavy_right_child);

    // only happens with deletion
    if heavy_right_child.balance_factor() == 0 {
        curr_root.set_balance_factor(curr_root.balance_factor() + 1);
        heavy_right_child.set_balance_factor(heavy_right_child.balance_factor() - 1);
    // happens with insertion or deletion
    } else {
        curr_root.set_balance_factor(0);
        heavy_right_child.set_balance_factor(0);
    }

    heavy_right_child
}

fn rotate_right_left<T: Ord>(
    curr_root: *mut AvlTreeNode<T>,
    curr_right_node_with_heavy_left: *mut AvlTreeNode<T>,
) -> *mut AvlTreeNode<T> {
    let curr_root = unsafe { &mut *curr_root };
    let curr_right_node_with_heavy_left = unsafe { &mut *curr_right_node_with_heavy_left };

    // curr_right_node_with_heavy_left is by 2 higher than its sibling
    let right_left_child = curr_right_node_with_heavy_left.left_child(); // Inner child of curr_right_node_with_heavy_left
    assert!(!right_left_child.is_null());
    let right_left_child = unsafe { &mut *right_left_child };
    // right_left_child is by 1 higher than sibling
    let right_left_right_child = right_left_child.right_child();

    curr_right_node_with_heavy_left.set_left_child(right_left_right_child);
    if !right_left_right_child.is_null() {
        unsafe { (*right_left_right_child).set_parent(curr_right_node_with_heavy_left) };
    }

    right_left_child.set_right_child(curr_right_node_with_heavy_left);
    curr_right_node_with_heavy_left.set_parent(right_left_child);

    let right_left_left_child = right_left_child.left_child();
    curr_root.set_right_child(right_left_left_child);
    if !right_left_left_child.is_null() {
        unsafe { (*right_left_left_child).set_parent(curr_root) };
    }

    right_left_child.set_left_child(curr_root);
    right_left_child.set_parent(curr_root.parent);
    curr_root.set_parent(right_left_child);

    // 1st case, BF(Y) == 0,
    //   only happens with deletion, not insertion:
    if right_left_child.balance_factor() == 0 {
        curr_root.set_balance_factor(0);
        curr_right_node_with_heavy_left.set_balance_factor(0);
    } else {
        // other cases happen with insertion or deletion:
        if right_left_child.balance_factor() > 0 {
            // t3 was higher
            curr_root.set_balance_factor(curr_root.balance_factor() - 1); // t1 now higher
            curr_right_node_with_heavy_left.set_balance_factor(0);
        } else {
            // t2 was higher
            curr_root.set_balance_factor(0);
            curr_right_node_with_heavy_left
                .set_balance_factor(curr_right_node_with_heavy_left.balance_factor() + 1); // t4 now higher
        }
    }

    right_left_child.set_balance_factor(0);
    // return new root of rotated subtree
    right_left_child
}

fn rotate_right<T: Ord>(
    curr_root: *mut AvlTreeNode<T>,
    heavy_left_child: *mut AvlTreeNode<T>,
) -> *mut AvlTreeNode<T> {
    let curr_root = unsafe { &mut *curr_root };
    let heavy_left_child = unsafe { &mut *heavy_left_child };

    unsafe {
        let left_right_child = heavy_left_child.right_child();

        curr_root.set_left_child(left_right_child);
        if !left_right_child.is_null() {
            (*left_right_child).set_parent(curr_root);
        }

        heavy_left_child.set_right_child(curr_root);
        heavy_left_child.set_parent(curr_root.parent);
        curr_root.set_parent(heavy_left_child);

        if heavy_left_child.balance_factor() == 0 {
            curr_root.set_balance_factor(curr_root.balance_factor() - 1);
            heavy_left_child.set_balance_factor(heavy_left_child.balance_factor() + 1);
        } else {
            curr_root.set_balance_factor(0);
            heavy_left_child.set_balance_factor(0);
        }

        heavy_left_child
    }
}

fn rotate_left_right<T: Ord>(
    curr_root: *mut AvlTreeNode<T>,
    curr_left_node_with_heavy_right: *mut AvlTreeNode<T>,
) -> *mut AvlTreeNode<T> {
    let curr_root = unsafe { &mut *curr_root };
    let curr_left_node_with_heavy_right = unsafe { &mut *curr_left_node_with_heavy_right };

    unsafe {
        // curr_right_node_with_heavy_left is by 2 higher than its sibling
        let left_right_child = curr_left_node_with_heavy_right.right_child(); // Inner child of curr_right_node_with_heavy_left
        let left_right_left_child = (*left_right_child).left_child();

        curr_left_node_with_heavy_right.set_right_child(left_right_left_child);
        if !left_right_left_child.is_null() {
            (*left_right_left_child).set_parent(curr_left_node_with_heavy_right);
        }

        (*left_right_child).set_left_child(curr_left_node_with_heavy_right);
        curr_left_node_with_heavy_right.set_parent(left_right_child);

        let left_right_right_child = (*left_right_child).right_child();
        curr_root.set_left_child(left_right_right_child);
        if !left_right_right_child.is_null() {
            (*left_right_right_child).set_parent(curr_root);
        }

        (*left_right_child).set_right_child(curr_root);
        (*left_right_child).set_parent(curr_root.parent);
        curr_root.set_parent(left_right_child);

        if (*left_right_child).balance_factor() == 0 {
            curr_root.set_balance_factor(0);
            curr_left_node_with_heavy_right.set_balance_factor(0);
        } else {
            if (*left_right_child).balance_factor() < 0 {
                curr_root.set_balance_factor(curr_root.balance_factor() - 1);
                curr_left_node_with_heavy_right.set_balance_factor(0);
            } else {
                curr_root.set_balance_factor(0);
                curr_left_node_with_heavy_right
                    .set_balance_factor(curr_left_node_with_heavy_right.balance_factor() + 1);
            }
        }

        (*left_right_child).set_balance_factor(0);
        // return new root of rotated subtree
        left_right_child
    }
}

#[derive(Debug)]
pub struct AvlTree<T: Ord> {
    root: *mut AvlTreeNode<T>,
}

// public APIs
impl<T: Ord> AvlTree<T> {
    pub fn new() -> Self {
        Self {
            root: core::ptr::null_mut(),
        }
    }

    pub fn insert(&mut self, key: T) {
        // EdgeCase: tree is empty
        if self.root.is_null() {
            self.root = Box::into_raw(Box::new(AvlTreeNode::new(key)));
            return;
        }

        // step 1. search down to the correct node and insert our new node at the right
        // child
        let mut curr: *mut AvlTreeNode<T> = self.root;
        loop {
            // SAFETY: we handle the root possibly being null in the
            // above check and when we find a null child below, we
            // break the loop
            let c = unsafe { &mut *curr };
            if key < c.data {
                if c.left_child().is_null() {
                    c.set_left_child(Box::into_raw(Box::new(AvlTreeNode::new(key))));
                    break;
                } else {
                    curr = c.left_child();
                }
            } else {
                if c.right_child().is_null() {
                    c.set_right_child(Box::into_raw(Box::new(AvlTreeNode::new(key))));
                    break;
                } else {
                    curr = c.right_child();
                }
            }
        }

        unsafe {
            let mut parent = (*curr).parent;
            let new_parent;
            let parent_parent;
            // step 2. balance tree upwards
            while !parent.is_null() {
                if curr == (*parent).right_child() {
                    // parent is right-heavy
                    if (*parent).balance_factor() > 0 {
                        parent_parent = (*parent).parent;
                        if (*curr).balance_factor() < 0 {
                            new_parent = rotate_right_left(parent, curr); // Double rotation: Right(Z) then Left(X)
                        } else {
                            new_parent = rotate_left(parent, curr); // Single rotation Left(X)
                        }
                        // After rotation adapt parent link
                    } else {
                        if (*parent).balance_factor() < 0 {
                            // parent absorbs curr's height increase
                            (*parent).set_balance_factor(0);
                            // we're now balanced. leave the loop
                            break;
                        }
                        (*parent).set_balance_factor((*parent).balance_factor() + 1);
                        curr = parent;
                        parent = (*curr).parent;
                        continue;
                    }
                } else {
                    // parent is left-heavy
                    if (*parent).balance_factor() < 0 {
                        parent_parent = (*parent).parent;
                        if (*curr).balance_factor() > 0 {
                            new_parent = rotate_left_right(parent, curr); // Double rotation: Left(Z) then Right(X)
                        } else {
                            new_parent = rotate_right(parent, curr); // Single rotation Right(X)
                        }
                    } else {
                        if (*parent).balance_factor() > 0 {
                            // parent absorbs curr's height increase
                            (*parent).set_balance_factor(0);
                            // we're balanced now. leave the loop
                            break;
                        }

                        (*parent).set_balance_factor((*parent).balance_factor() - 1);
                        curr = parent;
                        parent = (*curr).parent;
                        continue;
                    }
                }

                // After a rotation adapt parent link:
                // N is the new root of the rotated subtree
                // Height does not change: Height(N) == old Height(X)
                (*new_parent).set_parent(parent_parent);
                if parent_parent != core::ptr::null_mut() {
                    if parent == (*parent_parent).left_child() {
                        (*parent_parent).set_left_child(new_parent);
                    } else {
                        (*parent_parent).set_right_child(new_parent);
                    }
                } else {
                    // N is the new root of the total tree
                    self.root = new_parent;
                }

                // There is no fall thru, only break; or continue;
                break;
            }
        }
    }

    pub fn remove(&mut self, key: &T) -> Option<*mut AvlTreeNode<T>> {
        // EdgeCase: tree is empty
        if self.root.is_null() {
            return None;
        }

        // step 1. search down to the correct node and insert our new node at the right
        // child
        let mut curr: *mut AvlTreeNode<T> = self.root;
        loop {
            if curr.is_null() {
                return None;
            }

            // SAFETY: we handle the root possibly being null in the
            // above check and when we find a null child below, we
            // break the loop
            let c = unsafe { &mut *curr };
            if key == &c.data {
                if c.left_child().is_null() {
                    self.shift_nodes(c, c.right_child());
                } else if c.right_child().is_null() {
                    self.shift_nodes(c, c.left_child());
                } else {
                    let y = c.successor();
                    if unsafe { (*y).parent } != c {
                        self.shift_nodes(y, unsafe { (*y).right });
                        unsafe { (*y).right = c.right };
                        unsafe { (*(*y).right).parent = y };
                    }
                    self.shift_nodes(c, y);
                    unsafe { (*y).left = c.left };
                    unsafe { (*(*y).left).parent = y };
                }
                break;
            } else if key < &c.data {
                curr = c.left_child();
            } else {
                curr = c.right_child();
            }
        }

        let mut parent = unsafe { (*curr).parent() };
        let mut new_parent = core::ptr::null_mut();
        let mut parent_bf;

        while !parent.is_null() {
            // Save parent of X around rotations
            let parent_parent = unsafe { (*parent).parent() };
            // BF(X) has not yet been updated!
            // the left subtree decreases
            if curr == unsafe { (*parent).left_child() } {
                // X is right-heavy
                if unsafe { (*parent).balance_factor() } > 0 {
                    // ==> the temporary BF(X) == +2
                    // ==> rebalancing is required.
                    // Sibling of N (higher by 2)
                    let parent_right = unsafe { (*parent).right_child() };
                    parent_bf = unsafe { (*parent_right).balance_factor() };
                    // Right Left Case  (see figure 3)
                    if parent_bf < 0 {
                        // Double rotation: Right(Z) then Left(X)
                        new_parent = rotate_right_left(parent, parent_right);
                    } else {
                        // Right Right Case (see figure 2)
                        new_parent = rotate_left(parent, parent_right);
                    }
                    // After rotation adapt parent link
                } else {
                    if unsafe { (*parent).balance_factor() == 0 } {
                        unsafe { (*parent).set_balance_factor((*parent).balance_factor() + 1) };
                        break; // Leave the loop
                    }

                    // N = parent;
                    // BF(N) = 0; // Height(N) decreases by 1

                    curr = parent;
                    parent = unsafe { (*curr).parent };
                    continue;
                }
            // (N == right_child(X)): The right subtree decreases
            } else {
                // X is left-heavy
                if unsafe { (*parent).balance_factor() } < 0 {
                    // ==> the temporary BF(X) == -2
                    // ==> rebalancing is required.
                    // Sibling of N (higher by 2)
                    let parent_left = unsafe { (*parent).left_child() };
                    parent_bf = unsafe { (*parent_left).balance_factor() };
                    if parent_bf > 0 {
                        new_parent = rotate_left_right(parent, curr); // Double rotation: Left(Z) then Right(X)
                    } else {
                        // Left-Left Case
                        // Single-rotation Right(X)
                        new_parent = rotate_right(parent, curr);
                    }
                    // After rotation adapt parent link
                } else {
                    if unsafe { (*parent).balance_factor() } == 0 {
                        unsafe { (*parent).set_balance_factor((*parent).balance_factor() - 1) };
                        // Leave the loop
                        break;
                    }
                    curr = parent;
                    // Height(N) decreases by 1
                    unsafe { (*curr).set_balance_factor(0) };
                    continue;
                }
            }
            // After a rotation adapt parent link:
            // N is the new root of the rotated subtree
            unsafe { (*new_parent).set_parent(parent_parent) };
            if !parent_parent.is_null() {
                if parent == unsafe { (*parent_parent).left_child() } {
                    unsafe { (*parent_parent).set_left_child(new_parent) };
                } else {
                    unsafe { (*parent_parent).set_right_child(new_parent) };
                }
            } else {
                // N is the new root of the total tree
                self.root = new_parent;
            }

            if parent_bf == 0 {
                break; // Height does not change: Leave the loop
            }

            // Height(N) decreases by 1 (== old Height(X)-1)
        }

        // If (b != 0) the height of the total tree decreases by 1.
        Some(new_parent)
    }

    pub fn find(&self, key: &T) -> Option<&AvlTreeNode<T>> {
        // EdgeCase: tree is empty
        if self.root.is_null() {
            return None;
        }

        let mut curr: *mut AvlTreeNode<T> = self.root;
        loop {
            if curr.is_null() {
                return None;
            }

            // SAFETY: we handle the root possibly being null before starting the
            // loop and each iteration checks that curr is not null
            let c = unsafe { &mut *curr };
            if key == &c.data {
                return Some(c);
            } else if key < &c.data {
                curr = c.left_child();
            } else {
                curr = c.right_child();
            }
        }
    }

    pub fn iter(&self) -> AvlTreeIter<T> {
        let mut curr = self.root;

        while !curr.is_null() {
            // SAFETY:
            // we just verified that curr is not null
            let predecessor = unsafe { (*curr).predecessor() };
            if predecessor.is_null() {
                break;
            }
            curr = predecessor;
        }

        AvlTreeIter::new(curr)
    }

    fn shift_nodes(&mut self, curr: *mut AvlTreeNode<T>, mut to_shift: *mut AvlTreeNode<T>) {
        if unsafe { (*curr).parent.is_null() } {
            self.root = to_shift;
        } else if curr == unsafe { (*(*curr).parent).left } {
            unsafe { (*(*curr).parent).left = to_shift };
        } else {
            unsafe { (*(*curr).parent).right = to_shift };
        }

        if !to_shift.is_null() {
            // TODO BUG [matthew-russo] : this is a useless assignment which means
            // we're not properly shifting. we need to have a pointer to a pointer
            // rather than a copied pointer
            unsafe { to_shift = (*curr).parent };
            let _ = to_shift;
        }
    }
}

// private APIs
impl<T: Ord> AvlTree<T> {}

impl<T: Ord> Default for AvlTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct AvlTreeIter<'a, T: Ord> {
    curr_node: *mut AvlTreeNode<T>,
    lifetime: core::marker::PhantomData<&'a T>,
}

impl<'a, T: Ord> AvlTreeIter<'a, T> {
    fn new(curr_node: *mut AvlTreeNode<T>) -> Self {
        Self {
            curr_node,
            lifetime: core::marker::PhantomData,
        }
    }
}

impl<'a, T: Ord> Iterator for AvlTreeIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr_node.is_null() {
            return None;
        }

        let curr = unsafe { &(*self.curr_node).data };
        self.curr_node = unsafe { (*self.curr_node).successor() };
        Some(curr)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const SMALL_TEST_ARRAY: [u32; 4] = [42, 73, 19, 112];

    #[test]
    fn can_insert() {
        let mut tree = AvlTree::new();
        for i in SMALL_TEST_ARRAY {
            tree.insert(i);
        }
    }

    #[test]
    fn can_find() {
        let mut tree = AvlTree::new();
        for i in SMALL_TEST_ARRAY {
            tree.insert(i);
            tree.find(&i).expect("couldn't find value just inserted");
        }
    }

    #[test]
    fn can_remove() {
        let mut tree = AvlTree::new();
        for i in SMALL_TEST_ARRAY {
            tree.insert(42_u32);
            tree.remove(&42_u32)
                .expect("remove should have successfully removed node");
            assert!(tree.find(&42_u32).is_none())
        }
    }

    #[test]
    fn can_iterate() {
        let mut tree = AvlTree::new();

        for i in SMALL_TEST_ARRAY {
            tree.insert(i);
        }

        let mut sorted = SMALL_TEST_ARRAY.to_vec();
        sorted.sort();

        let mut ref_iter = sorted.iter();
        let mut tree_iter = tree.iter();

        loop {
            match (ref_iter.next(), tree_iter.next()) {
                (Some(ref_next), Some(tree_next)) => assert_eq!(ref_next, tree_next),
                (Some(ref_next), None) => panic!(
                    "Reference iter returned: {:?} but tree iter returned None",
                    ref_next
                ),
                (None, Some(tree_next)) => panic!(
                    "Tree iter returned: {:?} but reference iter returned None",
                    tree_next
                ),
                (None, None) => break,
            }
        }
    }
}

#[cfg(test)]
mod proptests {
    use std::collections::BTreeSet;

    use proptest::collection::vec;
    use proptest::prelude::*;
    use proptest_derive::Arbitrary;

    use super::*;

    #[derive(Arbitrary, Debug)]
    enum Operation {
        Insert(u32),
        Remove,
        Find,
        Iterate,
    }

    proptest! {
        #[test]
        #[ignore]
        fn longform(ops in vec(any::<Operation>(), 2048)) {
            println!("Executing {} operations against AvlTree\n\t{:?}", ops.len(), ops);

            let mut reference = BTreeSet::new();
            let mut tree = AvlTree::new();

            fn get_random(reference: &BTreeSet<u32>) -> Option<u32> {
                if reference.is_empty() {
                    return None;
                }

                let len = reference.len();
                let index_to_get = rand::thread_rng().gen_range(0..len);
                let to_return = reference.iter().nth(index_to_get).unwrap();
                Some(*to_return)
            }

            for op in ops.iter() {
                match op {
                    Operation::Insert(i) => {
                        reference.insert(*i);
                        tree.insert(*i);
                    }
                    Operation::Remove => {
                        if let Some(to_remove) = get_random(&reference) {
                            assert!(reference.remove(&to_remove));
                            assert!(tree.remove(&to_remove).is_some());
                        }
                    }
                    Operation::Find => {
                        if let Some(to_find) = get_random(&reference) {
                            assert_eq!(reference.get(&to_find).unwrap(), &to_find);
                            assert_eq!(tree.find(&to_find).unwrap().data, to_find);
                        }
                    }
                    Operation::Iterate => {
                        let mut ref_iter = reference.iter();
                        let mut tree_iter = tree.iter();
                        loop {
                            match (ref_iter.next(), tree_iter.next()) {
                                (Some(ref_next), Some(tree_next)) => assert_eq!(ref_next, tree_next),
                                (Some(ref_next), None) => panic!("Reference iter returned: {:?} but tree iter returned None", ref_next),
                                (None, Some(tree_next)) => panic!("Tree iter returned: {:?} but reference iter returned None", tree_next),
                                (None, None) => break,
                            }
                        }
                    }
                }
            }

            println!("Successfully executed {} operations against AvlTree\n\t{:?}", ops.len(), ops);
        }
    }
}

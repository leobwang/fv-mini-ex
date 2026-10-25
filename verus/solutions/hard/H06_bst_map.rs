// H06 | BST map | 1-2 h | Box, enum, Map view, union_prefer_right, decreases self, =~=
// GOAL
//   A binary search tree of u64 keys/values, viewed as a Map. Implement lookup, insert and delete
//   (by value: they consume the tree and return the new one) so the view behaves like a Map
//   and the BST ordering invariant `bst()` is preserved.
//
// REFERENCE
//   match self { Tree::Leaf => .., Tree::Node { left, key, val, right } => .. }  // move out fields
//   (*left).insert(k, v)  Box::new(t)                // unbox / rebox a subtree
//   t is Node   t->key   Tree::Node { .. }           // variant test, field access, wildcard pattern
//   m.union_prefer_right(m2)  m.insert(k, v)  m.remove(k)  m.dom().contains(k)  m[k]
//   assert(r.as_map() =~= self.as_map().insert(k, v));   // map equality, proved key by key
//   decreases self,                                  // recursion on a subtree terminates
//   unreached()                                      // value of a match arm the requires rule out
//   r is Some ==> r->0 == x                          // Option in specs
// NOTE: Z3 uses the bst() forall facts only when it sees a matching term, e.g. right.as_map().dom().contains(k).

use vstd::prelude::*;

verus! {

// BEGIN SPEC
enum Tree {
    Leaf,
    Node { left: Box<Tree>, key: u64, val: u64, right: Box<Tree> },
}

impl Tree {
    spec fn as_map(self) -> Map<u64, u64>
        decreases self,
    {
        match self {
            Tree::Leaf => Map::empty(),
            Tree::Node { left, key, val, right } =>
                left.as_map().union_prefer_right(right.as_map()).insert(key, val),
        }
    }

    spec fn bst(self) -> bool
        decreases self,
    {
        match self {
            Tree::Leaf => true,
            Tree::Node { left, key, val, right } => {
                &&& left.bst()
                &&& right.bst()
                &&& forall|k: u64| #[trigger] left.as_map().dom().contains(k) ==> k < key
                &&& forall|k: u64| #[trigger] right.as_map().dom().contains(k) ==> k > key
            },
        }
    }
}
// END SPEC

// MILESTONE (optional: change or delete)
proof fn lemma_go_left(t: Tree, k: u64)
    requires t.bst(), t is Node, k < t->key,
    ensures
        t.as_map().dom().contains(k) == t->left.as_map().dom().contains(k),
        t.as_map().dom().contains(k) ==> t.as_map()[k] == t->left.as_map()[k],
{
    assert(!t->right.as_map().dom().contains(k));
}

// MILESTONE (optional: change or delete)
proof fn lemma_go_right(t: Tree, k: u64)
    requires t.bst(), t is Node, k > t->key,
    ensures
        t.as_map().dom().contains(k) == t->right.as_map().dom().contains(k),
        t.as_map().dom().contains(k) ==> t.as_map()[k] == t->right.as_map()[k],
{
    assert(!t->left.as_map().dom().contains(k));
}

impl Tree {
    // BEGIN SPEC
    fn lookup(&self, k: u64) -> (r: Option<u64>)
        requires self.bst(),
        ensures
            r is Some <==> self.as_map().dom().contains(k),
            r is Some ==> r->0 == self.as_map()[k],
        decreases self,
    // END SPEC
    {
        match self {
            Tree::Leaf => None,
            Tree::Node { left, key, val, right } => {
                if k == *key {
                    Some(*val)
                } else if k < *key {
                    proof { lemma_go_left(*self, k); }
                    left.lookup(k)
                } else {
                    proof { lemma_go_right(*self, k); }
                    right.lookup(k)
                }
            },
        }
    }

    // BEGIN SPEC
    fn insert(self, k: u64, v: u64) -> (r: Tree)
        requires self.bst(),
        ensures r.bst(), r.as_map() == self.as_map().insert(k, v),
        decreases self,
    // END SPEC
    {
        match self {
            Tree::Leaf => {
                let r = Tree::Node { left: Box::new(Tree::Leaf), key: k, val: v, right: Box::new(Tree::Leaf) };
                assert(r.as_map() =~= self.as_map().insert(k, v));
                r
            },
            Tree::Node { left, key, val, right } => {
                if k == key {
                    Tree::Node { left, key, val: v, right }
                } else if k < key {
                    let nl = (*left).insert(k, v);
                    let r = Tree::Node { left: Box::new(nl), key, val, right };
                    // WHY: without this the forall in bst() about `right` never fires on k.
                    assert(!right.as_map().dom().contains(k));
                    assert(r.as_map() =~= self.as_map().insert(k, v));
                    r
                } else {
                    let nr = (*right).insert(k, v);
                    let r = Tree::Node { left, key, val, right: Box::new(nr) };
                    assert(r.as_map() =~= self.as_map().insert(k, v));
                    r
                }
            },
        }
    }

    // MILESTONE (optional: change or delete)
    // Remove the smallest key of a non-empty tree; returns (key, value, rest).
    fn remove_min(self) -> (r: (u64, u64, Tree))
        requires self.bst(), self is Node,
        ensures
            r.2.bst(),
            self.as_map().dom().contains(r.0),
            self.as_map()[r.0] == r.1,
            r.2.as_map() == self.as_map().remove(r.0),
            forall|k: u64| #[trigger] self.as_map().dom().contains(k) ==> r.0 <= k,
        decreases self,
    {
        match self {
            Tree::Leaf => { unreached() },
            Tree::Node { left, key, val, right } => {
                match *left {
                    Tree::Leaf => {
                        assert(left.as_map() =~= Map::empty());
                        assert(right.as_map() =~= self.as_map().remove(key));
                        (key, val, *right)
                    },
                    Tree::Node { .. } => {
                        let (mk, mv, nl) = (*left).remove_min();
                        let r = Tree::Node { left: Box::new(nl), key, val, right };
                        assert(!right.as_map().dom().contains(mk));
                        assert(r.as_map() =~= self.as_map().remove(mk));
                        (mk, mv, r)
                    },
                }
            },
        }
    }

    // BEGIN SPEC
    fn delete(self, k: u64) -> (r: Tree)
        requires self.bst(),
        ensures r.bst(), r.as_map() == self.as_map().remove(k),
        decreases self,
    // END SPEC
    {
        match self {
            Tree::Leaf => {
                assert(self.as_map() =~= self.as_map().remove(k));
                Tree::Leaf
            },
            Tree::Node { left, key, val, right } => {
                if k == key {
                    match *right {
                        Tree::Leaf => {
                            assert(right.as_map() =~= Map::empty());
                            assert(left.as_map() =~= self.as_map().remove(k));
                            *left
                        },
                        Tree::Node { .. } => {
                            let (mk, mv, nr) = (*right).remove_min();
                            let r = Tree::Node { left, key: mk, val: mv, right: Box::new(nr) };
                            assert(r.as_map() =~= self.as_map().remove(k));
                            r
                        },
                    }
                } else if k < key {
                    let nl = (*left).delete(k);
                    let r = Tree::Node { left: Box::new(nl), key, val, right };
                    assert(r.as_map() =~= self.as_map().remove(k));
                    r
                } else {
                    let nr = (*right).delete(k);
                    let r = Tree::Node { left, key, val, right: Box::new(nr) };
                    assert(r.as_map() =~= self.as_map().remove(k));
                    r
                }
            },
        }
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each operation is a structural recursion: match on self, recurse into the one subtree that
    can hold k, rebuild the Node. The other subtree cannot hold k by bst(): say so with an assert
    that mentions `other.as_map().dom().contains(k)` so the quantifier fires.
H2. After rebuilding, prove the view with `assert(r.as_map() =~= self.as_map().insert(k, v))`
    (or `.remove(k)`). For delete of the root key: if right is Leaf return *left; otherwise take
    the minimum (mk, mv) out of right with remove_min and make it the new root key/value.
    remove_min: if left is Leaf the root is the minimum; else recurse into left.
H3. insert, k < key branch:
      let nl = (*left).insert(k, v);
      let r = Tree::Node { left: Box::new(nl), key, val, right };
      assert(r.as_map() =~= self.as_map().insert(k, v));
      r
    lemma_go_left's proof is one line: assert(!t->right.as_map().dom().contains(k));
*/

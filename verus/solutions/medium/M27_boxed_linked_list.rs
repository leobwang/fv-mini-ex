// M27 | Boxed linked list | 10-15 min | enum with Box, recursive view, recursive exec fn, cursor loop
// GOAL
//   A cons list with a Seq view. Implement nth (recursively) and to_vec (with a loop that walks
//   a `&List` cursor down the list).
//
// REFERENCE
//   enum List { Nil, Cons(u64, Box<List>) }        // Box<List> derefs automatically in spec
//   match self { List::Nil => .., List::Cons(x, tail) => .. }   // x: &u64, tail: &Box<List>
//   fn f(&self, ..) -> .. decreases self, { .. tail.f(..) .. }  // recursion on a substructure
//   let mut cur: &List = self;  ...  cur = tail;                   // walk the list in a loop
//   loop invariant I, ensures Q, decreases cur.to_seq().len(), { .. break .. }  // Q: at break
//   *x                                              // copy the u64 out of a &u64

use vstd::prelude::*;

verus! {

// BEGIN SPEC
enum List {
    Nil,
    Cons(u64, Box<List>),
}

impl List {
    spec fn to_seq(&self) -> Seq<u64>
        decreases self,
    {
        match self {
            List::Nil => seq![],
            List::Cons(x, tail) => seq![*x] + tail.to_seq(),
        }
    }

    fn nth(&self, i: usize) -> (r: u64)
        requires i < self.to_seq().len(),
        ensures r == self.to_seq()[i as int],
// END SPEC
        decreases self,
    {
        match self {
            List::Nil => unreached(),
            List::Cons(x, tail) => {
                if i == 0 {
                    *x
                } else {
                    tail.nth(i - 1)
                }
            },
        }
    }

    // BEGIN SPEC
    fn to_vec(&self) -> (v: Vec<u64>)
        ensures v@ == self.to_seq(),
    // END SPEC
    {
        let mut v: Vec<u64> = Vec::new();
        let mut cur: &List = self;
        loop
            invariant v@ + cur.to_seq() == self.to_seq(),
            ensures v@ == self.to_seq(),
            decreases cur.to_seq().len(),
        {
            match cur {
                List::Nil => {
                    // WHY: the Seq equality needs ++ with the empty seq simplified.
                    assert(v@ + cur.to_seq() == v@);
                    break;
                },
                List::Cons(x, tail) => {
                    assert(v@.push(*x) + tail.to_seq() == v@ + cur.to_seq());
                    v.push(*x);
                    cur = tail;
                },
            }
        }
        v
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. nth: match on self. On Cons, index 0 is the head; otherwise recurse into the tail with i - 1.
    The Nil arm is impossible because i < len.
H2. to_vec: keep the invariant "what I pushed, followed by what is left, is the whole list".
    Use `loop` + `break` with `decreases cur.to_seq().len()`. After a `loop`, only its `ensures`
    is known (it must hold at every break).
H3. nth needs `decreases self,` and `List::Nil => unreached(),`.
    to_vec:  invariant v@ + cur.to_seq() == self.to_seq(),  ensures v@ == self.to_seq(),
    In the Cons arm, before pushing:  assert(v@.push(*x) + tail.to_seq() == v@ + cur.to_seq());
*/

// M16 | Stack with a Seq view | 10-15 min | impl View, closed spec fn view, &mut self, final(self)
// GOAL
//   Give Stack an abstract view (a Seq, top = last element) and implement its methods so
//   that the contracts, stated only in terms of the view, hold.
//
// REFERENCE
//   impl View for Stack { type V = Seq<u64>; closed spec fn view(&self) -> Seq<u64> { .. } }
//   s@                              // shorthand for s.view()
//   fn push(&mut self, x: u64) ensures final(self)@ == old(self)@.push(x),
//   self.items.push(x);  self.items.pop()   // Vec::pop returns Option<u64>
//   s.last()  s.drop_last()  Seq::<u64>::empty()
//   r is None     r == Some(x)      // Option in specs

use vstd::prelude::*;

verus! {

// BEGIN SPEC
struct Stack {
    items: Vec<u64>,
}

impl View for Stack {
    type V = Seq<u64>;

    closed spec fn view(&self) -> Seq<u64>
// END SPEC
    {
        Seq::empty() // TODO
    }
}

impl Stack {
    // BEGIN SPEC
    fn new() -> (s: Stack)
        ensures s@ == Seq::<u64>::empty(),
    // END SPEC
    {
        Stack { items: Vec::new() }
    }

    // BEGIN SPEC
    fn push(&mut self, x: u64)
        ensures final(self)@ == old(self)@.push(x),
    // END SPEC
    {

    }

    // BEGIN SPEC
    fn pop(&mut self) -> (r: Option<u64>)
        ensures
            old(self)@.len() == 0 ==> r is None && final(self)@ == old(self)@,
            old(self)@.len() > 0 ==> r == Some(old(self)@.last()) && final(self)@ == old(self)@.drop_last(),
    // END SPEC
    {
        None // TODO
    }

    // BEGIN SPEC
    fn peek(&self) -> (r: Option<u64>)
        ensures
            self@.len() == 0 ==> r is None,
            self@.len() > 0 ==> r == Some(self@.last()),
    // END SPEC
    {
        None // TODO
    }

    // BEGIN SPEC
    fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    // END SPEC
    {
        0 // TODO
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The view is the abstraction of the representation: what Seq does `items` stand for?
H2. With view = items@, every method is one line using the matching Vec operation; Vec's own
    contracts (push, pop, len, indexing) give exactly the Seq facts you need.
H3. closed spec fn view(&self) -> Seq<u64> { self.items@ }
    push: self.items.push(x);   pop: self.items.pop()
*/

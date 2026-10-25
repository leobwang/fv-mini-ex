// H05 | Linked stack | 45-90 min | Option<Box<Node>>, recursive view, take, struct invariant, list reversal
// GOAL
//   A singly linked stack of u64 with a cached length. Implement len, push, pop, to_vec and an
//   in-place reverse (relink the nodes; no Vec). The view is the Seq of values from the head.
//
// REFERENCE
//   spec fn f(l: Option<Box<Node>>) -> nat decreases l { match l { None => 0, Some(n) => 1 + f(n.next) } }
//   let h = self.head.take();                   // h == old head, self.head becomes None
//   Some(Box::new(Node { val: x, next: h }))    // allocate a node in front of h
//   let node = cur.unwrap();  let n = *node;    // unwrap requires `cur is Some`; *node moves out of the Box
//   while cur.is_some() invariant ... decreases list_view(cur).len(),
//   match l { None => {}, Some(node) => { push_all(out, &node.next); } }  // l: &Option<Box<Node>>
//   fn push_all(..) ensures .. decreases list_view(*l).len(),   // recursive exec needs decreases
//   s.reverse()   s.drop_first()   seq![x] + s   // Seq ops used by the specs
// NOTE: in `ensures`, write `old(self)@` / `final(self)@`; `self.len` must stay equal to the view's length.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
struct Node {
    val: u64,
    next: Option<Box<Node>>,
}

struct Stack {
    head: Option<Box<Node>>,
    len: usize,
}

spec fn list_view(l: Option<Box<Node>>) -> Seq<u64>
    decreases l,
{
    match l {
        None => Seq::empty(),
        Some(n) => seq![n.val] + list_view(n.next),
    }
}

impl View for Stack {
    type V = Seq<u64>;

    closed spec fn view(&self) -> Seq<u64> {
        list_view(self.head)
    }
}

impl Stack {
    spec fn well_formed(&self) -> bool {
        self.len == self@.len()
    }

    fn len(&self) -> (r: usize)
        requires
            self.well_formed(),
        ensures
            r == self@.len(),
// END SPEC
    {
        0 // TODO
    }

// BEGIN SPEC
    fn push(&mut self, x: u64)
        requires
            old(self).well_formed(),
            old(self)@.len() < usize::MAX,
        ensures
            final(self).well_formed(),
            final(self)@ == seq![x] + old(self)@,
// END SPEC
    {
    }

// BEGIN SPEC
    fn pop(&mut self) -> (r: Option<u64>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            old(self)@.len() == 0 ==> r is None && final(self)@ == old(self)@,
            old(self)@.len() > 0 ==> r == Some(old(self)@[0]) && final(self)@ == old(self)@.drop_first(),
// END SPEC
    {
        None // TODO
    }

// BEGIN SPEC
    fn to_vec(&self) -> (r: Vec<u64>)
        ensures
            r@ == self@,
// END SPEC
    {
        Vec::new() // TODO
    }

// BEGIN SPEC
    fn reverse(&mut self)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.reverse(),
// END SPEC
    {
    }
}

// MILESTONE (optional: change or delete)
// Append the values of list l to out (recursion on the list, by shared reference).
fn push_all(out: &mut Vec<u64>, l: &Option<Box<Node>>)
    ensures
        final(out)@ == old(out)@ + list_view(*l),
{
}

// MILESTONE (optional: change or delete)
// Moving the front of `cur` onto `rev` keeps rev.reverse() + cur unchanged.
// (Verus may prove this one by itself; the work is finding the statement and calling it.)
proof fn lemma_reverse_cons(r: Seq<u64>, x: u64, c: Seq<u64>)
    ensures
        (seq![x] + r).reverse() + c == r.reverse() + (seq![x] + c),
{
}

// MILESTONE (optional: change or delete)
proof fn lemma_reverse_reverse(s: Seq<u64>)
    ensures
        s.reverse().reverse() == s,
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. push/pop are a few lines each with take(). to_vec walks the list by shared reference
    (push_all, or a loop over `cur: &Option<Box<Node>>`). reverse is the classic loop: detach the
    list into `cur`, keep a reversed prefix in `rev`, move one node at a time from cur to rev.
H2. Loop invariant for reverse: old(self)@ == list_view(rev).reverse() + list_view(cur), plus a
    length fact. lemma_reverse_cons is exactly the step; lemma_reverse_reverse finishes (when cur
    is None, list_view(rev).reverse() == old(self)@, so list_view(rev) == old(self)@.reverse()).
H3. Loop:
      let mut cur = self.head.take(); let mut rev: Option<Box<Node>> = None;
      while cur.is_some()
          invariant old(self)@ == list_view(rev).reverse() + list_view(cur),
                    list_view(rev).len() + list_view(cur).len() == old(self).len,
          decreases list_view(cur).len(),
      { let node = cur.unwrap(); let n = *node;
        proof { lemma_reverse_cons(list_view(rev), n.val, list_view(n.next)); }
        cur = n.next; rev = Some(Box::new(Node { val: n.val, next: rev })); }
    push_all: `match l { None => {}, Some(node) => { out.push(node.val); push_all(out, &node.next); } }`
    with `decreases list_view(*l).len()`.
*/

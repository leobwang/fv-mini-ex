// H04 | Ring buffer queue | 30-60 min | struct invariant, View, Seq::new, wrap-around indices, &mut self
// GOAL
//   Implement a fixed-capacity FIFO queue on a circular Vec. The abstract value (view) is the
//   Seq of queued elements, front first. You also write the struct invariant well_formed: make it
//   strong enough that every method can be verified against the view.
//
// REFERENCE
//   impl View for RingBuffer { type V = Seq<u64>; closed spec fn view(&self) -> Seq<u64> { .. } }
//   self@  /  old(self)@  /  final(self)@        // the view of the current / entry / exit value
//   Seq::new(n, |i: int| f(i))                   // the Seq of length n with entries f(0..n)
//   s.push(x)   s.drop_first()   s[0]            // queue operations on the view
//   vec![0u64; n]                                 // a Vec of n zeros (ensures v@.len() == n)
//   self.buf.set(k, x);                           // write through &mut self
//   fn m(&mut self) requires old(self).well_formed() ensures final(self).well_formed(), ...
//   let r = RingBuffer { buf: b, head: 0, len: 0 };   // struct literal
//   &&& P  &&& Q                                  // conjunction, one clause per line
// NOTE: head + len can exceed usize::MAX in theory; compute the wrap with cap - head instead.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
struct RingBuffer {
    buf: Vec<u64>,
    head: usize,
    len: usize,
}

impl RingBuffer {
    spec fn capacity(&self) -> nat {
        self.buf.len() as nat
    }

    /// Physical position of logical index i (no `%`, so arithmetic stays linear).
    spec fn phys(&self, i: int) -> int {
        if self.head + i < self.buf.len() {
            self.head + i
        } else {
            self.head + i - self.buf.len()
        }
    }

    /// The struct invariant: you choose the body.
    spec fn well_formed(&self) -> bool
// END SPEC
    {
        &&& self.buf.len() > 0
        &&& self.head < self.buf.len()
        &&& self.len <= self.buf.len()
    }
}

// BEGIN SPEC
impl View for RingBuffer {
    type V = Seq<u64>;

    closed spec fn view(&self) -> Seq<u64> {
        Seq::new(self.len as nat, |i: int| self.buf[self.phys(i)])
    }
}

impl RingBuffer {
    fn new(cap: usize) -> (r: RingBuffer)
        requires
            cap > 0,
        ensures
            r.well_formed(),
            r@ == Seq::<u64>::empty(),
            r.capacity() == cap,
// END SPEC
    {
        RingBuffer { buf: vec![0u64; cap], head: 0, len: 0 }
    }

// BEGIN SPEC
    fn len(&self) -> (r: usize)
        requires
            self.well_formed(),
        ensures
            r == self@.len(),
// END SPEC
    {
        self.len
    }

// BEGIN SPEC
    fn get(&self, i: usize) -> (r: u64)
        requires
            self.well_formed(),
            i < self@.len(),
        ensures
            r == self@[i as int],
// END SPEC
    {
        let k = self.phys_index(i);
        self.buf[k]
    }

// BEGIN SPEC
    fn push_back(&mut self, x: u64)
        requires
            old(self).well_formed(),
            old(self)@.len() < old(self).capacity(),
        ensures
            final(self).well_formed(),
            final(self).capacity() == old(self).capacity(),
            final(self)@ == old(self)@.push(x),
// END SPEC
    {
        let k = self.phys_index(self.len);
        self.buf.set(k, x);
        self.len = self.len + 1;
    }

// BEGIN SPEC
    fn pop_front(&mut self) -> (r: u64)
        requires
            old(self).well_formed(),
            old(self)@.len() > 0,
        ensures
            final(self).well_formed(),
            final(self).capacity() == old(self).capacity(),
            r == old(self)@[0],
            final(self)@ == old(self)@.drop_first(),
// END SPEC
    {
        let r = self.buf[self.head];
        self.head = self.next_index(self.head);
        self.len = self.len - 1;
        r
    }

    // MILESTONE (optional: change or delete)
    // Overflow-safe exec version of phys.
    fn phys_index(&self, i: usize) -> (r: usize)
        requires
            self.well_formed(),
            i < self.buf.len(),
        ensures
            r == self.phys(i as int),
            r < self.buf.len(),
    {
        let t = self.buf.len() - self.head;
        if i < t { self.head + i } else { i - t }
    }

    // MILESTONE (optional: change or delete)
    // The slot after k, wrapping to 0 at the end of buf.
    fn next_index(&self, k: usize) -> (r: usize)
        requires
            self.well_formed(),
            k < self.buf.len(),
        ensures
            r < self.buf.len(),
            r == if k + 1 == self.buf.len() { 0 } else { k + 1 },
    {
        if k + 1 == self.buf.len() { 0 } else { k + 1 }
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. new: buf = vec![0u64; cap]. len/get are one-liners once phys_index exists. The work is in
    push_back (write at phys(len), len += 1) and pop_front (read buf[head], advance head, len -= 1).
    well_formed must say what those index computations rely on.
H2. well_formed: buf is non-empty, head is a valid slot, len fits in buf. phys_index: compare i
    with cap - head (never overflows) instead of computing head + i. With the right code, Verus
    proves the Seq view equalities pointwise on its own.
H3. well_formed: `&&& self.buf.len() > 0 &&& self.head < self.buf.len() &&& self.len <= self.buf.len()`.
    phys_index: `let t = self.buf.len() - self.head; if i < t { self.head + i } else { i - t }`.
    push_back: `let k = self.phys_index(self.len); self.buf.set(k, x); self.len = self.len + 1;`
    pop_front: `let r = self.buf[self.head]; self.head = self.next_index(self.head);
    self.len = self.len - 1; r`.
*/

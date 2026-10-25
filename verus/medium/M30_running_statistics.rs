// M30 | Running statistics | 10-15 min | struct invariant, Ghost field, &mut self, sum spec
// GOAL
//   Stats keeps count, total and max of all values added so far; the ghost field `seen` records
//   them. Implement `add` so that `well_formed` is preserved.
//
// REFERENCE
//   struct S { n: u64, seen: Ghost<Seq<u64>> }   // Ghost field: spec-only, erased at runtime
//   self.seen@                                    // the Seq inside the Ghost
//   self.seen = Ghost(self.seen@.push(x));        // update a ghost field from exec code
//   requires old(self).well_formed(), ensures final(self).well_formed(),
//   assert(s.push(x).drop_last() =~= s);          // needed to unfold sum(s.push(x))
// NOTE: total + x may overflow u64; the precondition rules that out. Check max separately.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sum(s: Seq<u64>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum(s.drop_last()) + s.last() }
}

struct Stats {
    count: u64,
    total: u64,
    max: u64,
    seen: Ghost<Seq<u64>>,
}

impl Stats {
    spec fn well_formed(&self) -> bool {
        &&& self.count == self.seen@.len()
        &&& self.total == sum(self.seen@)
        &&& forall|i: int| 0 <= i < self.seen@.len() ==> self.seen@[i] <= self.max
        &&& self.seen@.len() == 0 ==> self.max == 0
        &&& self.seen@.len() > 0 ==> exists|i: int| 0 <= i < self.seen@.len() && self.seen@[i] == self.max
    }

    fn new() -> (s: Stats)
        ensures s.well_formed(), s.seen@ == Seq::<u64>::empty(),
    {
        Stats { count: 0, total: 0, max: 0, seen: Ghost(Seq::empty()) }
    }

    fn add(&mut self, x: u64)
        requires
            old(self).well_formed(),
            old(self).count < u64::MAX,
            old(self).total + x <= u64::MAX,
        ensures
            final(self).well_formed(),
            final(self).seen@ == old(self).seen@.push(x),
// END SPEC
    {
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Update the three exec fields, then the ghost field. The total follows from how sum unfolds
    on a pushed sequence.
H2. max: take x when the stats were empty or x is bigger. Verus has to see that sum(s.push(x))
    unfolds to sum(s) + x, which needs s.push(x).drop_last() to be recognized as s.
H3. assert(self.seen@.push(x).drop_last() =~= self.seen@);
    if self.count == 0 || x > self.max { self.max = x; }
    self.count = self.count + 1;  self.total = self.total + x;
    self.seen = Ghost(self.seen@.push(x));
*/

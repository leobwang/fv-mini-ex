// E36 | Interval intersection | 2-3 min | impl, &self methods, spec methods
// GOAL
//   Intersect two closed integer intervals. An interval with lo > hi is empty.
//
// REFERENCE
//   impl S {
//       spec fn p(&self, x: int) -> bool { self.a <= x }     // spec method
//       fn m(&self, o: &S) -> (r: S) ensures r.p(0) { .. }   // exec method with a contract
//   }
//   S { a: 1, b: 2 }                                         // struct literal

use vstd::prelude::*;

verus! {

// BEGIN SPEC
struct Interval {
    lo: i64,
    hi: i64,
}

impl Interval {
    spec fn contains(&self, x: int) -> bool {
        self.lo <= x <= self.hi
    }

    fn intersect(&self, other: &Interval) -> (r: Interval)
        ensures forall|x: int| r.contains(x) <==> self.contains(x) && other.contains(x),
// END SPEC
    {
        Interval { lo: 0, hi: 0 } // TODO
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The intersection of [a, b] and [c, d] is [max(a, c), min(b, d)].
H2. Empty results need no special case: lo > hi already means empty.
H3. Interval { lo: if self.lo >= other.lo { self.lo } else { other.lo }, hi: (the min) }
*/

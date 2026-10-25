// E04 | Average without overflow | 2-3 min | int, as int, overflow
// GOAL
//   Return the floor of the average of a and b, for every pair of u64 values.
//
// REFERENCE
//   a as int + b as int          // spec arithmetic is on mathematical `int`: it never overflows
//   (a + b) / 2                  // in exec code this is checked: a + b may exceed u64::MAX
//   a / 2, a % 2                 // u64 division/remainder never overflow
//   / and % by a literal are understood by the solver automatically (linear arithmetic).
// NOTE: the obvious (a + b) / 2 is rejected with "possible arithmetic overflow".

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn average(a: u64, b: u64) -> (r: u64)
    ensures r == (a as int + b as int) / 2,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Avoid ever forming a + b in u64.
H2. Halve each argument separately, then correct for the case where both are odd.
H3. a / 2 + b / 2 + (a % 2 + b % 2) / 2   (or: if a <= b { a + (b - a) / 2 } else { ... })
*/

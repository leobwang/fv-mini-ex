// E05 | Saturating add | 1-3 min | u64::MAX, overflow-safe comparison
// GOAL
//   Add a and b, returning u64::MAX instead of overflowing.
//
// REFERENCE
//   u64::MAX                       // usable in exec code and in specs
//   if a > u64::MAX - b { .. }     // test for overflow without performing the overflowing add
//   In ensures, `a + b` is an `int`, so `a + b > u64::MAX` is meaningful.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn sat_add(a: u64, b: u64) -> (r: u64)
    ensures
        a + b <= u64::MAX ==> r == a + b,
        a + b > u64::MAX ==> r == u64::MAX,
// END SPEC
{
    if a > u64::MAX - b { u64::MAX } else { a + b }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The check itself must not overflow. Which subtraction is always safe?
H2. u64::MAX - b never underflows; compare a against it.
H3. if a > u64::MAX - b { u64::MAX } else { a + b }
*/

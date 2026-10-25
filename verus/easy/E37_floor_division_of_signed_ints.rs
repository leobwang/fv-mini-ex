// E37 | Floor division of signed ints | 2-3 min | exec vs spec division
// GOAL
//   Compute floor(x / 2) for an i64. The spec uses mathematical division.
//
// REFERENCE
//   spec:  x / 2, x % 2      // on int: rounds toward -infinity; x % 2 is 0 or 1
//   exec:  x / 2, x % 2      // on i64: Rust semantics, rounds toward 0; x % 2 may be -1
//   (-7) / 2 is -4 in spec but -3 in exec.
// NOTE: returning x / 2 directly fails for odd negative x.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn half_floor(x: i64) -> (r: i64)
    ensures r == x / 2,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Try x = -7: what does each side compute?
H2. Exec x / 2 is correct except for negative odd x, where it is one too large.
H3. if x >= 0 || x % 2 == 0 { x / 2 } else { x / 2 - 1 }
*/

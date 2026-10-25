// E02 | Max of two | 1-2 min | if-else expression, || in ensures [R02]
// GOAL
//   Return the larger of a and b.
//
// REFERENCE
//   ensures r >= a, r == a || r == b,        // clauses are and-ed; `||`, `&&`, `!` as in Rust
//   let m = if a >= b { a } else { b };      // `if` is an expression; both branches must type-check

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn max2(a: i64, b: i64) -> (r: i64)
    ensures r >= a, r >= b, r == a || r == b,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare a and b once.
H2. Check that each branch satisfies all three ensures clauses.
H3. if a >= b { a } else { b }
*/

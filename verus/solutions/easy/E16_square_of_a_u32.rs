// E16 | Square of a u32 | 2-3 min | by (nonlinear_arith), overflow
// GOAL
//   Square a u32 into a u64. You must convince Verus the product cannot overflow.
//
// REFERENCE
//   let y = x as u64;                                    // widening cast in exec code
//   assert(y * y <= 100) by (nonlinear_arith)
//       requires y <= 10;                                // the nonlinear prover sees ONLY these facts
//   The default solver mode treats y * y as opaque; nonlinear_arith turns on
//   multiplication reasoning for one assertion.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn square(x: u32) -> (r: u64)
    ensures r == x * x,
// END SPEC
{
    let y = x as u64;
    assert(y * y <= u64::MAX) by (nonlinear_arith)
        requires y <= u32::MAX;
    y * y
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Writing (x as u64) * (x as u64) alone fails with "possible arithmetic overflow".
H2. Bound the product before computing it, using y <= u32::MAX.
H3. assert(y * y <= u64::MAX) by (nonlinear_arith) requires y <= u32::MAX;
*/

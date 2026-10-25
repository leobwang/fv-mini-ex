// M10 | Integer square root | 10-15 min | nonlinear_arith, widening to u64, overflow [R12]
// GOAL
//   Return floor(sqrt(n)): the r with r*r <= n < (r+1)*(r+1). The spec is over unbounded
//   int; the code must not overflow (a u32 squared can need 64 bits).
//
// REFERENCE
//   let r1 = r as u64 + 1;  r1 * r1 <= n as u64     // compute squares in a wider type
//   assert(r1 * r1 <= 0x1_0000_0000) by (nonlinear_arith) requires r1 <= 0x1_0000;
//   assert(r < 0x1_0000) by (nonlinear_arith) requires (r + 1) * (r + 1) <= n, n < 0x1_0000_0000;
//       // a contradiction-style bound: a big r would make its square too big
//   decreases 0x1_0000 - r      // a measure that shrinks as r grows
// NOTE: the loop condition is overflow-checked using only the invariant.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn isqrt(n: u32) -> (r: u32)
    ensures
        r * r <= n,
        n < (r + 1) * (r + 1),
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Count r up from 0 while (r+1)^2 <= n. Do the squaring in u64.
H2. Invariant: r*r <= n, a bound r < 2^16 (gives a decreasing measure), and
    (r+1)*(r+1) <= 2^32 so the loop TEST cannot overflow. After the loop the negated test is
    exactly n < (r+1)^2.
H3. invariant r * r <= n, r < 0x1_0000, (r + 1) * (r + 1) <= 0x1_0000_0000,
    decreases 0x1_0000 - r. In the body, with r1 = r + 1:
      assert(r1 < 0x1_0000) by (nonlinear_arith) requires r1 * r1 <= n, n < 0x1_0000_0000, r1 > 0;
      assert((r1 + 1) * (r1 + 1) <= 0x1_0000_0000) by (nonlinear_arith) requires r1 < 0x1_0000, r1 > 0;
*/

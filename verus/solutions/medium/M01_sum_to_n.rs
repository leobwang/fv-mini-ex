// M01 | Sum 0..n by a loop | 5-10 min | while, invariant, nonlinear_arith, overflow [R03]
// GOAL
//   Compute 0 + 1 + ... + n with a loop (no closed formula in the code) and prove the
//   result equals n(n+1)/2. The precondition bounds n so every partial sum fits in u64.
//
// REFERENCE
//   while i < n invariant P(i), Q(i), decreases n - i, { ... }   // all facts the loop needs
//   assert(x * (y + 1) == x * y + x) by (nonlinear_arith);   // products of variables need this
//   assert(a * b <= c) by (nonlinear_arith) requires a <= 10, b <= 10, c == 100;   // with hyps
//   s <= i * 1_000_000      // a variable times a literal is linear: fine without help
// NOTE: loops only see their invariant: restate the bound on n inside it.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn sum_to_n(n: u64) -> (r: u64)
    requires n <= 1_000_000,
    ensures r == n * (n + 1) / 2,
// END SPEC
{
    let mut s: u64 = 0;
    let mut i: u64 = 0;
    while i < n
        invariant
            i <= n <= 1_000_000,
            2 * s == i * (i + 1),
            s <= i * 1_000_000,  // WHY: lets Verus prove `s + i` cannot overflow
        decreases n - i,
    {
        assert((i + 1) * (i + 2) == i * (i + 1) + 2 * (i + 1)) by (nonlinear_arith);
        i = i + 1;
        s = s + i;
    }
    s
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep a counter i and an accumulator s; the invariant links s to i, not to n.
H2. Invariant: i <= n, the bound on n, `2 * s == i * (i + 1)`, and an upper bound on s for overflow.
    The step from i to i + 1 is a nonlinear identity; state it with `by (nonlinear_arith)`.
H3. invariant i <= n <= 1_000_000, 2 * s == i * (i + 1), s <= i * 1_000_000,
    and in the body, before updating:
    assert((i + 1) * (i + 2) == i * (i + 1) + 2 * (i + 1)) by (nonlinear_arith);
*/

// E35 | Evaluate by computation | 1-2 min | by (compute)
// GOAL
//   Prove two concrete values of recursive spec fns without unfolding by hand.
//
// REFERENCE
//   assert(f(10) == 55) by (compute);   // evaluate the expression with Verus's interpreter
//   Works on closed terms (no free variables) built from spec fns, literals and arithmetic.
//   Compare E09, where the solver had to be walked through each unfolding.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

spec fn tri(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { n + tri((n - 1) as nat) }
}

proof fn concrete_values()
    ensures
        pow2(40) == 1099511627776,
        tri(100) == 5050,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Forty asserts would work, but there is a one-liner per clause.
H2. Each clause is a closed term: no variables.
H3. assert(pow2(40) == 1099511627776) by (compute); assert(tri(100) == 5050) by (compute);
*/

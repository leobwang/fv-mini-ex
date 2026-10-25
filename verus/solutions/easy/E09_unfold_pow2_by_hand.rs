// E09 | Unfold pow2 by hand | 1-3 min | assert, fuel
// GOAL
//   Prove pow2(4) == 16 with a chain of assert statements.
//
// REFERENCE
//   assert(P);          // prove P at this point; afterwards P is a known fact
//   A recursive spec fn unfolds only ONE level per occurrence ("fuel 1"):
//   proving pow2(4) == 16 needs the values of pow2(3), pow2(2), ... to be known first.
// BANNED: compute, compute_only, reveal_with_fuel

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn pow2_4()
    ensures pow2(4) == 16,
// END SPEC
{
    assert(pow2(0) == 1);
    assert(pow2(1) == 2);
    assert(pow2(2) == 4);
    assert(pow2(3) == 8);
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start from the bottom of the recursion.
H2. Each assert should need just one unfolding plus the previous assert.
H3. assert(pow2(0) == 1); assert(pow2(1) == 2); assert(pow2(2) == 4); assert(pow2(3) == 8);
*/

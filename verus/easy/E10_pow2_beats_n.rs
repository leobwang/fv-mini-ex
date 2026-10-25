// E10 | pow2 beats n | 2-3 min | induction in a proof fn, decreases
// GOAL
//   Prove pow2(n) > n for every natural n, by induction.
//
// REFERENCE
//   proof fn lemma(n: nat) ensures P(n),
//       decreases n,                    // a recursive proof needs a measure, like a spec fn
//   { if n > 0 { lemma((n - 1) as nat); } }   // the recursive call is the induction hypothesis
// NOTE: `decreases` goes below the frozen region, just before the body.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_gt(n: nat)
    ensures pow2(n) > n,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The base case n == 0 is automatic; the step needs the fact for n - 1.
H2. Recursive call on n - 1, guarded by n > 0, plus `decreases n`.
H3. decreases n, { if n > 0 { lemma_pow2_gt((n - 1) as nat); } }
*/

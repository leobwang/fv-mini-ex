// E18 | A power of two above n | 1-3 min | assert-by, proving exists
// GOAL
//   Prove that some power of two exceeds n. lemma_pow2_gt (E10) is provided.
//
// REFERENCE
//   assert(P) by { lemma(x); }     // the block's facts stay local; only P is kept afterwards
//   To prove `exists|k: nat| Q(k)`, make Q(w) a known fact for some concrete w.
//   The solver matches on the trigger term (here pow2(k)), so pow2(w) must appear.

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
    decreases n,
{
    // Provided (this is E10).
    if n > 0 {
        lemma_pow2_gt((n - 1) as nat);
    }
}

proof fn exists_pow2_above(n: nat)
    ensures exists|k: nat| pow2(k) > n,
// END SPEC
{
    assert(pow2(n) > n) by {
        lemma_pow2_gt(n);
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Which k works? The provided lemma suggests one.
H2. Establish pow2(w) > n for your witness w; the exists then follows.
H3. assert(pow2(n) > n) by { lemma_pow2_gt(n); }
*/

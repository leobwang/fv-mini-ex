// E26 | Next power of two | 2-3 min | let ghost, ghost updates
// GOAL
//   Return the smallest power of two that is >= n. The exponent exists only in the proof.
//
// REFERENCE
//   let ghost mut k: nat = 0;        // ghost local: erased at runtime, may be int/nat/Seq/...
//   proof { k = k + 1; }             // ghost variables are updated inside proof blocks
//   invariant p == pow2(k),          // ghost locals may appear in invariants
//   decreases e,                     // e must stay >= 0 after each iteration, too

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

fn next_pow2(n: u64) -> (r: u64)
    requires 1 <= n <= 0x4000_0000_0000_0000,
    ensures
        r >= n,
        r < 2 * n,
        exists|k: nat| r == pow2(k),
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Double p starting from 1 until it reaches n.
H2. Track the exponent in a ghost variable so that p == pow2(k) can be an invariant.
H3. invariant 1 <= n <= 0x4000_0000_0000_0000, p == pow2(k), 1 <= p < 2 * n, decreases 2 * n - p,
*/

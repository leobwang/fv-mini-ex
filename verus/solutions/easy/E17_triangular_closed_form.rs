// E17 | Triangular closed form | 2-3 min | proof block in exec code
// GOAL
//   Compute tri(n) = 0 + 1 + ... + n in O(1) with n * (n + 1) / 2.
//   lemma_tri is provided; call it from exec code.
//
// REFERENCE
//   proof { lemma_tri(k); }       // ghost block inside an exec fn: may call proof fns
//   assert(P) by (nonlinear_arith) requires Q;      // from E16, for the overflow bound
//   Exec code cannot call a proof fn directly; wrap the call in proof { }.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn tri(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { n + tri((n - 1) as nat) }
}

proof fn lemma_tri(n: nat)
    ensures 2 * tri(n) == n * (n + 1),
    decreases n,
{
    // Provided.
    if n > 0 {
        lemma_tri((n - 1) as nat);
        assert(2 * tri(n) == n * (n + 1)) by (nonlinear_arith)
            requires
                n > 0,
                tri(n) == n + tri((n - 1) as nat),
                2 * tri((n - 1) as nat) == (n - 1) * n;
    }
}

fn tri_fast(n: u32) -> (r: u64)
    ensures r == tri(n as nat),
// END SPEC
{
    let m = n as u64;
    proof {
        lemma_tri(n as nat);
    }
    assert(m * (m + 1) <= u64::MAX) by (nonlinear_arith)
        requires m <= u32::MAX;
    m * (m + 1) / 2
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two things to justify: the formula (lemma_tri) and that m * (m + 1) fits in u64.
H2. Widen n to u64 first; (2^32 - 1) * 2^32 < 2^64.
H3. proof { lemma_tri(n as nat); }  assert(m * (m + 1) <= u64::MAX) by (nonlinear_arith) requires m <= u32::MAX;
*/

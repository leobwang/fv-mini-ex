// M25 | Ackermann grows | 10-15 min | lexicographic decreases, nested induction
// GOAL
//   Prove ack(m, n) > n for all m, n, and the closed form ack(1, n) == n + 2.
//   The recursive calls in ack decrease (m, n) lexicographically; so must your proof's.
//
// REFERENCE
//   proof fn lemma(m: nat, n: nat) ensures ... decreases m, n, { ... }   // lexicographic measure
//   // A recursive call lemma(m2, n2) is allowed when m2 < m, or m2 == m && n2 < n.
//   lemma((m - 1) as nat, ack(m, (n - 1) as nat));   // arguments may be any spec expression
// NOTE: `decreases` is not part of the frozen signature: you write it after the spec block.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn ack(m: nat, n: nat) -> nat
    decreases m, n,
{
    if m == 0 {
        n + 1
    } else if n == 0 {
        ack((m - 1) as nat, 1)
    } else {
        ack((m - 1) as nat, ack(m, (n - 1) as nat))
    }
}

proof fn lemma_ack_gt(m: nat, n: nat)
    ensures ack(m, n) > n,
// END SPEC
{
}

// BEGIN SPEC
proof fn lemma_ack_one(n: nat)
    ensures ack(1, n) == n + 2,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Follow the three branches of ack. The m == 0 case is free.
H2. For m > 0, n > 0: ack(m, n) = ack(m-1, k) with k = ack(m, n-1). You need k > n - 1
    (inner call) and ack(m-1, k) > k (outer call). Both are smaller in (m, n) lexicographically.
H3. decreases m, n,   then for m > 0:
      n == 0:  lemma_ack_gt((m - 1) as nat, 1);
      n > 0:   lemma_ack_gt(m, (n - 1) as nat);
               lemma_ack_gt((m - 1) as nat, ack(m, (n - 1) as nat));
    lemma_ack_one is a plain induction on n (decreases n); unfold ack(0, _) with an assert,
    e.g. assert(ack(0, 1) == 2) for n == 0 (each recursive spec call unfolds only once).
*/

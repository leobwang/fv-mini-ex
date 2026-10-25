// M35 | Integer log2 | 10-15 min | halving loop, nonlinear invariant, by (nonlinear_arith)
// GOAL
//   floor(log2 n): halve m = n until it reaches 1, counting the steps r. Prove
//   pow2(r) <= n < pow2(r + 1).
//
// REFERENCE
//   invariant pow2(r as nat) * m <= n, n < pow2(r as nat) * (m + 1), ...
//   assert(2 * p * (m / 2) <= p * m) by (nonlinear_arith) requires p >= 0, m >= 0;
//   // inside `by (nonlinear_arith)` only the listed `requires` facts are known
//   let ghost p = pow2(r as nat);         // name a spec value to keep asserts short
// NOTE: products of two variables (pow2(r) * m) are nonlinear; Verus needs help to move them.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

fn ilog2(n: u64) -> (r: u64)
    requires n >= 1,
    ensures pow2(r as nat) <= n < pow2(r as nat + 1),
// END SPEC
{
    let mut m: u64 = n;
    let mut r: u64 = 0;
    assert(pow2(0) == 1);
    while m > 1
        invariant
            m >= 1,
            r + m <= n,       // WHY: bounds r, so r + 1 cannot overflow
            pow2(r as nat) * m <= n,
            n < pow2(r as nat) * (m + 1),
        decreases m,
    {
        let ghost p = pow2(r as nat);
        assert(2 * p * (m / 2) <= p * m) by (nonlinear_arith) requires p >= 0, m >= 0;
        assert(p * (m + 1) <= 2 * p * (m / 2 + 1)) by (nonlinear_arith) requires p >= 0, m >= 0;
        m = m / 2;
        r = r + 1;
    }
    let ghost p = pow2(r as nat);
    assert(p * m == p && p * (m + 1) == 2 * p) by (nonlinear_arith) requires m == 1;
    assert(pow2(r as nat + 1) == 2 * p);
    r
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Think of n as sandwiched: pow2(r) * m <= n < pow2(r) * (m + 1). At m == 1 that is the goal.
H2. When m becomes m / 2 and pow2(r) doubles, both sides need a nonlinear step:
    2p(m/2) <= pm and p(m+1) <= 2p(m/2 + 1). Also add an invariant that bounds r (r + m <= n works).
    After the loop, m == 1; turn p * 1 and p * 2 into p and 2 * p the same way.
H3. invariant m >= 1, r + m <= n, pow2(r as nat) * m <= n, n < pow2(r as nat) * (m + 1)
    in the body, with  let ghost p = pow2(r as nat);
      assert(2 * p * (m / 2) <= p * m) by (nonlinear_arith) requires p >= 0, m >= 0;
      assert(p * (m + 1) <= 2 * p * (m / 2 + 1)) by (nonlinear_arith) requires p >= 0, m >= 0;
*/

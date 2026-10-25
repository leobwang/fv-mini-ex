// M24 | Powers-of-two table | 10-15 min | proof block in a loop, lemma call, by (compute), overflow
// GOAL
//   Build the table t[i] == 2^i for i < n (n <= 64) in a u64 Vec, doubling as you go.
//   The hard part is convincing Verus that `p * 2` never overflows.
//
// REFERENCE
//   proof { lemma_pow2_mono(i as nat, 62); }        // call a lemma from exec code
//   assert(pow2(62) == 0x4000_0000_0000_0000) by (compute);   // evaluate a closed term
//   while i < n invariant i < n ==> p == pow2(i as nat), ... decreases n - i, { ... }
//   t.push(p);                                       // t@ becomes old t@ with p appended
// NOTE: pow2(i) for i <= 62 fits with room to double; pow2(63) * 2 does not.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_mono(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b,
{
    if a < b {
        lemma_pow2_mono(a, (b - 1) as nat);
    }
}

fn pow2_table(n: usize) -> (t: Vec<u64>)
    requires n <= 64,
    ensures
        t.len() == n,
        forall|i: int| 0 <= i < n ==> t[i] == pow2(i as nat),
// END SPEC
{
    let mut t: Vec<u64> = Vec::new();
    let mut p: u64 = 1;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n <= 64,
            t.len() == i,
            i < n ==> p == pow2(i as nat),
            forall|j: int| 0 <= j < i ==> t[j] == pow2(j as nat),
        decreases n - i,
    {
        t.push(p);
        if i + 1 < n {
            proof {
                // WHY: i <= 62 here, so 2 * pow2(i) <= 2^63 fits in u64.
                lemma_pow2_mono(i as nat, 62);
                assert(pow2(62) == 0x4000_0000_0000_0000) by (compute);
            }
            p = p * 2;
        }
        i += 1;
    }
    t
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep p == pow2(i) and push p each round. Only double p when another entry is still needed,
    otherwise the last doubling (2^63 * 2) would overflow.
H2. Before `p = p * 2` you need p <= 2^62. Get it from the monotonicity lemma plus the concrete
    value of pow2(62), computed with `by (compute)`.
H3. invariant  i <= n, n <= 64, t.len() == i, i < n ==> p == pow2(i as nat),
               forall|j: int| 0 <= j < i ==> t[j] == pow2(j as nat)
    and before doubling:  proof { lemma_pow2_mono(i as nat, 62);
                                  assert(pow2(62) == 0x4000_0000_0000_0000) by (compute); }
*/

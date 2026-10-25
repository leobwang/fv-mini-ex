// M39 | Checked sum of a Vec | 15-20 min | Option, prefix-sum invariant, monotonicity lemma
// GOAL
//   Sum v in a u64, or return None if the true (mathematical) sum does not fit.
//   None must be honest: the WHOLE sum exceeds u64::MAX, not just some prefix of it.
//
// REFERENCE
//   if acc > u64::MAX - v[i] { return None; }      // overflow test that cannot itself overflow
//   match a.checked_add(b) { Some(c) => .., None => .. }   // alternative: std spec'd checked_add
//   invariant acc == sum(v@.subrange(0, i as int)), ...
//   proof fn lemma(s: Seq<u64>, k: int) requires 0 <= k <= s.len() ensures ... decreases s.len(), {..}
//   assert(s.subrange(0, k) =~= s.drop_last().subrange(0, k));   // prefix of the shorter Seq
// NOTE: elements are non-negative, so a prefix's sum is at most the whole sum. Prove that.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sum(s: Seq<u64>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum(s.drop_last()) + s.last() }
}

fn checked_sum(v: &Vec<u64>) -> (r: Option<u64>)
    ensures
        match r {
            Some(t) => t == sum(v@),
            None => sum(v@) > u64::MAX,
        },
// END SPEC
{
    let mut acc: u64 = 0;
    for i in 0..v.len()
        invariant acc == sum(v@.subrange(0, i as int)),
    {
        assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
        if acc > u64::MAX - v[i] {
            proof { lemma_prefix_le(v@, i + 1); }
            return None;
        }
        acc = acc + v[i];
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    Some(acc)
}

proof fn lemma_prefix_le(s: Seq<u64>, k: int)
    requires 0 <= k <= s.len(),
    ensures sum(s.subrange(0, k)) <= sum(s),
    decreases s.len(),
{
    if k == s.len() {
        assert(s.subrange(0, k) =~= s);
    } else {
        assert(s.subrange(0, k) =~= s.drop_last().subrange(0, k));
        lemma_prefix_le(s.drop_last(), k);
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep acc == sum of the prefix v[..i]. Before adding v[i], test whether it would overflow.
H2. On overflow, sum(prefix of length i + 1) > u64::MAX. To conclude sum(v@) > u64::MAX you need
    a lemma: sum(s.subrange(0, k)) <= sum(s). Prove it by induction on s.len(), dropping the last
    element whenever k < s.len().
H3. proof fn lemma_prefix_le(s: Seq<u64>, k: int) requires 0 <= k <= s.len()
        ensures sum(s.subrange(0, k)) <= sum(s) decreases s.len()
      { if k == s.len() { assert(s.subrange(0, k) =~= s); }
        else { assert(s.subrange(0, k) =~= s.drop_last().subrange(0, k)); lemma_prefix_le(s.drop_last(), k); } }
    loop body starts with  assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
*/

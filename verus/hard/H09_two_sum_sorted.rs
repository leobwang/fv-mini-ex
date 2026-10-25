// H09 | Two-sum on a sorted Vec | 30-60 min | two pointers, multi-trigger, pair-exclusion invariant, overflow
// GOAL
//   Given a sorted Vec and a target t, return indices i < j with v[i] + v[j] == t, or None if no
//   such pair exists. Use the two-pointer scan (lo from the left, hi from the right), O(n).
//
// REFERENCE
//   forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]   // two-index quantifier
//   #[trigger] s[i] + #[trigger] s[j]     // multi-trigger: fires when both s[i] and s[j] appear
//   assert forall|i: int, j: int| P(i, j) implies Q(i, j) by { if i == lo { assert(s[j] <= s[hi]); } }
//   match r { Some((i, j)) => .., None => .. }    // destructure a tuple option in ensures
//   return Some((lo, hi));                // early return from inside the loop
//   proof { lemma_drop_lo(v@, t, lo as int, hi as int); }   // call a lemma from exec code
// NOTE: v[lo] + v[hi] can overflow u64; check v[hi] <= t first, then compare v[lo] with t - v[hi].

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn two_sum(v: &Vec<u64>, t: u64) -> (r: Option<(usize, usize)>)
    requires sorted(v@),
    ensures
        match r {
            Some((i, j)) => i < j < v.len() && v[i as int] + v[j as int] == t,
            None => forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] + v[j] != t,
        },
// END SPEC
{
    None // TODO
}

// MILESTONE (optional: change or delete)
// Loop invariant: every pair that leaves the window [lo, hi] has been ruled out.
spec fn no_pair_outside(s: Seq<u64>, t: u64, lo: int, hi: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() && (i < lo || j > hi) ==>
        #[trigger] s[i] + #[trigger] s[j] != t
}

// MILESTONE (optional: change or delete)
proof fn lemma_drop_lo(s: Seq<u64>, t: u64, lo: int, hi: int)
    requires sorted(s), 0 <= lo < hi < s.len(), no_pair_outside(s, t, lo, hi), s[lo] + s[hi] < t,
    ensures no_pair_outside(s, t, lo + 1, hi),
{
}

// MILESTONE (optional: change or delete)
proof fn lemma_drop_hi(s: Seq<u64>, t: u64, lo: int, hi: int)
    requires sorted(s), 0 <= lo < hi < s.len(), no_pair_outside(s, t, lo, hi), s[lo] + s[hi] > t,
    ensures no_pair_outside(s, t, lo, hi - 1),
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. If v[lo] + v[hi] < t, then v[lo] is too small to pair with anything in (lo, hi] (all <= v[hi]),
    so lo can move right. If the sum is > t, v[hi] is too big for anything in [lo, hi).
H2. Invariant: lo <= hi < v.len(), sorted(v@), no_pair_outside(v@, t, lo, hi). When lo == hi
    the window holds no pair, so no_pair_outside is exactly the None postcondition. Handle
    v.len() == 0 before the loop (hi = v.len() - 1 would underflow).
H3. lemma_drop_lo: assert forall|i: int, j: int| 0 <= i < j < s.len() && (i < lo + 1 || j > hi)
      implies #[trigger] s[i] + #[trigger] s[j] != t by { if i == lo && j <= hi { assert(s[j] <= s[hi]); } }
    Loop body: let a = v[lo]; let b = v[hi]; if b > t { hi -= 1 } else if a == t - b { return Some((lo, hi)) }
    else if a < t - b { lo += 1 } else { hi -= 1 }   (each move after the matching lemma call).
*/

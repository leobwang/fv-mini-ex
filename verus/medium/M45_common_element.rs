// M45 | Common element of sorted Vecs | 10-15 min | two pointers, pair-exclusion invariant
// GOAL
//   Decide whether two sorted Vecs share a value, in one linear pass with two indices.
//
// REFERENCE
//   while i < a.len() && j < b.len() invariant ..., decreases a.len() - i + b.len() - j, { .. }
//   forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < b.len() && (p < i || q < j) ==> a[p] != b[q]
//   // loops only see their invariant: restate sorted(a@), sorted(b@) there
//   exists|i: int, j: int| P(i, j)          // two witnesses; `return true` at a match supplies them

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn has_common(a: &Vec<u64>, b: &Vec<u64>) -> (r: bool)
    requires sorted(a@), sorted(b@),
    ensures r <==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j],
// END SPEC
{
    false // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare a[i] and b[j]: equal means done; otherwise advance the side with the smaller value.
H2. The invariant says every pair with p < i or q < j is a mismatch. Advancing i past a[i] < b[j]
    is safe: a[i] < b[j] <= b[q] for every q >= j (sorted b).
H3. invariant i <= a.len(), j <= b.len(), sorted(a@), sorted(b@),
      forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < b.len() && (p < i || q < j) ==> a[p] != b[q],
    decreases a.len() - i + b.len() - j
*/

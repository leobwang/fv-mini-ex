// E45 | Ends of a sorted Vec | 1-2 min | spec predicate in requires, Seq::contains
// GOAL
//   Return the minimum and maximum of a non-empty sorted Vec in O(1).
//
// REFERENCE
//   spec fn sorted(s: Seq<u64>) -> bool { forall|i: int, j: int| .. }   // a predicate
//   requires sorted(v@),          // predicates make readable contracts
//   s.contains(x)                 // exists|i| 0 <= i < s.len() && s[i] == x
//   r.0, r.1                      // tuple fields

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

fn ends(v: &Vec<u64>) -> (r: (u64, u64))
    requires
        v.len() > 0,
        sorted(v@),
    ensures
        v@.contains(r.0),
        v@.contains(r.1),
        forall|i: int| 0 <= i < v.len() ==> r.0 <= v[i] && v[i] <= r.1,
// END SPEC
{
    (v[0], v[v.len() - 1])
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. In a sorted sequence, where are the extremes?
H2. The first and last elements; sortedness gives both bounds.
H3. (v[0], v[v.len() - 1])
*/

// E31 | Swap keeps the multiset | 1-2 min | broadcast use, to_multiset
// GOAL
//   Prove that swapping two positions of a Seq keeps its multiset of elements.
//
// REFERENCE
//   s.update(i, x)                 // Seq with position i replaced by x
//   s.to_multiset(), m.count(x)    // multiset of elements; the "permutation" spec
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;   // enable a lemma group
//   `broadcast use` inside a proof body enables the group there; at module level, everywhere.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
proof fn swap_multiset(s: Seq<int>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. vstd already knows how update interacts with to_multiset; the fact is just not enabled.
H2. The group group_to_multiset_ensures in vstd::seq_lib contains to_multiset_update.
H3. broadcast use vstd::seq_lib::group_to_multiset_ensures;
*/

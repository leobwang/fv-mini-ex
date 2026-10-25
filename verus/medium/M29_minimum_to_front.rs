// M29 | Minimum to front | 10-15 min | to_multiset, permutation, swap, ghost witness
// GOAL
//   Move a minimum element to index 0 by finding its index and swapping it with v[0].
//   The result must be a permutation of the input (same multiset) with v[0] <= every element.
//
// REFERENCE
//   s.to_multiset()                              // Multiset<T>; equal multisets = permutation
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;  // facts incl. update/push
//   //   s.update(i, a).to_multiset() == s.to_multiset().insert(a).remove(s[i])
//   let a = v[i]; let b = v[j]; v.set(i, b); v.set(j, a);   // swap via two sets
//   assert(v@ == old(v)@.update(0, x).update(m as int, y));  // name the state as updates

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn min_to_front(v: &mut Vec<i64>)
    requires v.len() > 0,
    ensures
        final(v).len() == old(v).len(),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        forall|i: int| 0 <= i < final(v).len() ==> final(v)[0] <= #[trigger] final(v)[i],
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two phases: a loop that finds an index m of a minimum, then one swap of v[0] and v[m].
H2. The loop invariant says v[m] <= every element seen so far. For the multiset, enable the
    to_multiset facts with `broadcast use` and let Verus see the result as two updates.
H3. for i in 1..v.len() invariant m < v.len(), forall|j: int| 0 <= j < i ==> v[m as int] <= v[j]
    after the swap:  assert(v@ == old(v)@.update(0, b).update(m as int, a));
*/

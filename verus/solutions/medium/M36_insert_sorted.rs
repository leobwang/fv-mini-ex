// M36 | Insert into sorted Vec | 15-20 min | sorted + multiset, Vec::insert, index shifting
// GOAL
//   Insert x into a sorted Vec so that it stays sorted. The new contents must be the old
//   multiset plus x.
//
// REFERENCE
//   v.insert(i, x);                    // final(v)@ == old(v)@.insert(i as int, x), needs i <= len
//   s.insert(i, x)[k]                  // = s[k] for k < i, x at i, s[k - 1] for k > i
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;   // incl. s.insert(i, a).to_multiset()
//   assert forall|a: int, b: int| 0 <= a < b < w.len() implies w[a] <= w[b] by { ... }
// NOTE: find the position first (a loop), then insert once.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn insert_sorted(v: &mut Vec<u64>, x: u64)
    requires sorted(v@),
    ensures
        sorted(final(v)@),
        final(v)@.to_multiset() == old(v)@.to_multiset().insert(x),
// END SPEC
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;

    let mut i: usize = 0;
    while i < v.len() && v[i] <= x
        invariant
            i <= v.len(),
            v@ == old(v)@,
            forall|k: int| 0 <= k < i ==> v[k] <= x,
        decreases v.len() - i,
    {
        i += 1;
    }
    let ghost s = v@;
    // WHY: everything from i on is > x (sorted, and v[i] > x when i < len).
    assert(forall|k: int| i <= k < s.len() ==> x < s[k]) by {
        assert forall|k: int| i <= k < s.len() implies x < s[k] by {
            assert(s[i as int] <= s[k]);
        }
    }
    v.insert(i, x);
    assert forall|a: int, b: int| 0 <= a < b < v.len() implies v[a] <= v[b] by {
        assert(v@ == s.insert(i as int, x));
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Scan i forward while v[i] <= x; then everything before i is <= x and everything from i on
    is > x (by sortedness). Insert at i.
H2. The multiset part comes from the to_multiset broadcast group. For sortedness of
    s.insert(i, x), prove the forall over pairs (a, b) with assert forall; the cases a < i, a == i,
    a > i follow from the facts about s and the index shift.
H3. loop: while i < v.len() && v[i] <= x
          invariant i <= v.len(), v@ == old(v)@, forall|k: int| 0 <= k < i ==> v[k] <= x
    then with  let ghost s = v@;  prove  forall|k: int| i <= k < s.len() ==> x < s[k]
    (use s[i] <= s[k]), insert, and finish with
    assert forall|a: int, b: int| 0 <= a < b < v.len() implies v[a] <= v[b] by { assert(v@ == s.insert(i as int, x)); }
*/

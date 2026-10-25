// M13 | Dedup a sorted Vec | 15-20 min | strictly increasing output, Seq::contains, ghost reasoning [R16]
// GOAL
//   Given a sorted Vec, return its distinct elements: strictly increasing, and containing
//   exactly the same values as the input.
//
// REFERENCE
//   s.contains(x)                 // exists|i: int| 0 <= i < s.len() && s[i] == x
//   r[r.len() - 1]                // exec: last element (only when r.len() > 0)
//   forall|x: u64| r@.contains(x) <==> v@.subrange(0, i as int).contains(x)   // set equality so far
//   assert(v@.subrange(0, i + 1) == v@.subrange(0, i as int).push(v[i as int]));
//   broadcast use vstd::seq_lib::group_seq_properties;   // file level: facts like
//       // s.push(y).contains(x) <==> s.contains(x) || x == y
// NOTE: loops do not see `requires`: restate sortedness in the invariant.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn dedup(v: &Vec<u64>) -> (r: Vec<u64>)
    requires sorted(v@),
    ensures
        forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] < r[j],
        forall|x: u64| r@.contains(x) <==> v@.contains(x),
// END SPEC
{
    Vec::new() // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Push v[i] unless it equals the last element pushed (duplicates are adjacent: v is sorted).
H2. Invariant: output strictly increasing; output contains exactly the values of the prefix
    v[0..i); and the output's last element is v[i-1] (so a new v[i] >= v[i-1] that differs
    from it is strictly larger). Grow the prefix with a subrange/push equality, and add
    `broadcast use vstd::seq_lib::group_seq_properties;` at file level for push/contains facts.
H3. invariant sorted(v@), forall|a: int, b: int| 0 <= a < b < r.len() ==> r[a] < r[b],
        forall|x: u64| r@.contains(x) <==> v@.subrange(0, i as int).contains(x),
        i > 0 ==> r.len() > 0 && r[r.len() - 1] == v[i - 1],  i == 0 ==> r.len() == 0,
*/

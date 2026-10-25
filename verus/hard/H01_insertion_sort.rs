// H01 | Insertion sort | 45-75 min | in-place sort, swap, to_multiset, nested loops, milestones [R14]
// GOAL
//   Sort a Vec<u64> in place by insertion sort. The result must be sorted AND a permutation of
//   the input (same multiset of elements).
//
// REFERENCE
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;  // to_multiset facts for push/update/...
//   s.update(i, x)                              // Seq with position i replaced by x
//   v.set(i, x);                                // final(v)@ == old(v)@.update(i as int, x)
//   while j > 0 && v[j - 1] > v[j]              // && short-circuits, so v[j - 1] is in bounds
//   forall|a: int, b: int| 0 <= a <= b < n ==> s[a] <= s[b]   // two bound variables
//   proof { lemma_swap_multiset(v@, i as int, j as int); }    // lemma on the current view
//   fn step(v: &mut Vec<u64>, i: usize) ensures final(v).len() == old(v).len(), ...
// NOTE: a `for i in 1..n` loop has the invariant `1 <= i` false when n == 0; start at 0.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

fn insertion_sort(v: &mut Vec<u64>)
    ensures
        sorted(final(v)@),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
// END SPEC
{
}

/// The first n elements of s are sorted.
spec fn sorted_prefix(s: Seq<u64>, n: int) -> bool {
    forall|a: int, b: int| 0 <= a <= b < n ==> s[a] <= s[b]
}

// MILESTONE (optional: change or delete)
proof fn lemma_swap_multiset(s: Seq<u64>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
}

// MILESTONE (optional: change or delete)
// Insert v[i] into the sorted prefix v[0..i] by swapping it leftwards.
fn insert_step(v: &mut Vec<u64>, i: usize)
    requires
        i < v.len(),
        sorted_prefix(v@, i as int),
    ensures
        final(v).len() == old(v).len(),
        sorted_prefix(final(v)@, i + 1),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        forall|k: int| i < k < final(v).len() ==> final(v)[k] == old(v)[k],
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two milestones do the work: swapping keeps the multiset, and one insertion step extends the
    sorted prefix by one. The main function is then a loop `for i in 0..n` calling insert_step.
H2. In insert_step, j is the current position of the element being inserted. Invariant shape:
    everything in v[0..=i] except position j is sorted, and v[j] is smaller than everything in
    v[j+1..=i]. The multiset and the untouched tail v[i+1..] are carried along.
H3. Inner-loop invariant:
      forall|a: int, b: int| 0 <= a <= b <= i && a != j && b != j ==> v[a] <= v[b],
      forall|k: int| j < k <= i ==> v[j as int] < v[k],
    lemma_swap_multiset's body is just `broadcast use vstd::seq_lib::group_to_multiset_ensures;`.
    Outer invariant: v.len() == n, sorted_prefix(v@, i as int), v@.to_multiset() == old(v)@.to_multiset().
*/

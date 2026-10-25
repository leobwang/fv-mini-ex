// H02 | Merge sort | 1-2 h | recursion, decreases, subrange, to_multiset, merge, milestones [R20]
// GOAL
//   Return a sorted copy of v by top-down merge sort. The result must be sorted AND have the same
//   multiset of elements as v.
//
// REFERENCE
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;  // s.push(x).to_multiset() == ..insert(x)
//   vstd::seq_lib::lemma_multiset_commutative(a, b);  // (a + b).to_multiset() == a.to_multiset().add(b.to_multiset())
//   assert(s.subrange(0, i + 1) =~= s.subrange(0, i).push(s[i]));  // =~= needed inside to_multiset(..)
//   m1.add(m2)    Seq::<u64>::empty()           // multiset union; the empty Seq
//   fn sort_range(v: &Vec<u64>, lo: usize, hi: usize) -> (r: Vec<u64>) ... decreases hi - lo,
//   let mid = lo + (hi - lo) / 2;                 // overflow-safe midpoint
//   while i < a.len() || j < b.len() ... decreases a.len() + b.len() - i - j,
//   r@.last()                                    // last element of a Seq (needs len > 0)
// NOTE: recursion in exec code needs its own `decreases` clause, just like a loop.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

fn merge_sort(v: &Vec<u64>) -> (r: Vec<u64>)
    ensures
        sorted(r@),
        r@.to_multiset() == v@.to_multiset(),
// END SPEC
{
    Vec::new() // TODO
}

// MILESTONE (optional: change or delete)
fn merge(a: &Vec<u64>, b: &Vec<u64>) -> (r: Vec<u64>)
    requires
        sorted(a@),
        sorted(b@),
    ensures
        sorted(r@),
        r@.to_multiset() == a@.to_multiset().add(b@.to_multiset()),
{
    Vec::new() // TODO
}

// MILESTONE (optional: change or delete)
// Sort the slice v[lo..hi] into a fresh Vec.
fn sort_range(v: &Vec<u64>, lo: usize, hi: usize) -> (r: Vec<u64>)
    requires
        lo <= hi <= v.len(),
    ensures
        sorted(r@),
        r@.to_multiset() == v@.subrange(lo as int, hi as int).to_multiset(),
{
    Vec::new() // TODO
}

// MILESTONE (optional: change or delete)
proof fn lemma_split_multiset(s: Seq<u64>, lo: int, mid: int, hi: int)
    requires
        0 <= lo <= mid <= hi <= s.len(),
    ensures
        s.subrange(lo, hi).to_multiset()
            == s.subrange(lo, mid).to_multiset().add(s.subrange(mid, hi).to_multiset()),
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do the milestones bottom-up: lemma_split_multiset, merge, sort_range, then merge_sort is
    sort_range(v, 0, v.len()) plus one =~= fact about v@.subrange(0, len).
H2. merge: two indices i, j; push the smaller head. Invariant: r is sorted, r's multiset is
    a[0..i] + b[0..j], and r's last element is <= both remaining heads. sort_range: base cases
    hi - lo <= 1 (empty / one element), else recurse on both halves, merge, lemma_split_multiset.
H3. merge invariant (plus i <= a.len(), j <= b.len(), sorted(r@)):
      r@.to_multiset() == a@.subrange(0, i as int).to_multiset().add(b@.subrange(0, j as int).to_multiset()),
      r.len() > 0 ==> (i < a.len() ==> r@.last() <= a[i as int]) && (j < b.len() ==> r@.last() <= b[j as int]),
    After each push assert `a@.subrange(0, i + 1) =~= a@.subrange(0, i).push(a[i])` (with casts).
    lemma_split_multiset: assert(s.subrange(lo, hi) =~= s.subrange(lo, mid) + s.subrange(mid, hi))
    then call lemma_multiset_commutative on the two halves.
*/

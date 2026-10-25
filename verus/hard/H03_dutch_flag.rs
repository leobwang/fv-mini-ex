// H03 | Dutch national flag | 40-70 min | 3-way partition, swap, to_multiset, region invariants [R19]
// GOAL
//   Rearrange v in place around a pivot p (Dijkstra's Dutch national flag): first all elements
//   < p, then all == p, then all > p. Return the two region boundaries. One pass, swaps only.
//
// REFERENCE
//   fn f(v: &mut Vec<i64>) -> (r: (usize, usize))   // named tuple result; use r.0 and r.1 in ensures
//   (lo, hi)                                      // build the tuple to return
//   let a = v[i]; let b = v[j]; v.set(i, b); v.set(j, a);   // swap two positions
//   s.update(i, s[j]).update(j, s[i])             // the view after swapping positions i and j
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;  // to_multiset of update/push/...
//   while mid < hi invariant ... decreases hi - mid,
//   hi -= 1;                                     // usize: Verus checks hi > 0 first
// NOTE: three indices lo <= mid <= hi: [0,lo) < p, [lo,mid) == p, [mid,hi) unknown, [hi,n) > p.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn dutch_flag(v: &mut Vec<i64>, p: i64) -> (r: (usize, usize))
    ensures
        final(v).len() == old(v).len(),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        r.0 <= r.1 <= final(v).len(),
        forall|i: int| 0 <= i < r.0 ==> final(v)[i] < p,
        forall|i: int| r.0 <= i < r.1 ==> final(v)[i] == p,
        forall|i: int| r.1 <= i < final(v).len() ==> final(v)[i] > p,
// END SPEC
{
    (0, 0) // TODO
}

// MILESTONE (optional: change or delete)
proof fn lemma_swap_multiset(s: Seq<i64>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
}

// MILESTONE (optional: change or delete)
fn swap(v: &mut Vec<i64>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        final(v)@ == old(v)@.update(i as int, old(v)[j as int]).update(j as int, old(v)[i as int]),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep three indices lo <= mid <= hi. Look at v[mid]: smaller than p goes to the front region,
    equal stays, larger goes to the back region. Each step shrinks the unknown region [mid, hi).
H2. Small case first: if v[mid] < p, swap(lo, mid) and advance both; if == p, advance mid; if > p,
    decrement hi and swap(mid, hi) without advancing mid (the new v[mid] is still unknown).
H3. Loop invariant:
      v.len() == n, lo <= mid <= hi <= n, v@.to_multiset() == old(v)@.to_multiset(),
      forall|i: int| 0 <= i < lo ==> v[i] < p,
      forall|i: int| lo <= i < mid ==> v[i] == p,
      forall|i: int| hi <= i < n ==> v[i] > p,
    swap: `proof { lemma_swap_multiset(v@, i as int, j as int); }` BEFORE the two v.set calls
    (the lemma talks about the view before the swap).
*/

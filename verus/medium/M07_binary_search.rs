// M07 | Binary search | 10-15 min | sorted Vec, half-open window, overflow-safe midpoint [R09]
// GOAL
//   Search a sorted Vec. Some(i) must point at key; None must mean key is absent.
//
// REFERENCE
//   let mid = lo + (hi - lo) / 2;      // (lo + hi) / 2 can overflow usize; Verus rejects it
//   while lo < hi invariant lo <= hi <= v.len(), ..., decreases hi - lo, { ... }
//   forall|i: int| 0 <= i < lo ==> v[i] < key       // everything left of the window is too small
//   forall|i: int| hi <= i < v.len() ==> v[i] > key // everything right of it is too big
// NOTE: loops do not see `requires`: restate sortedness in the invariant.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn binary_search(v: &Vec<u64>, key: u64) -> (r: Option<usize>)
    requires forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
    ensures
        match r {
            Some(i) => i < v.len() && v[i as int] == key,
            None => forall|i: int| 0 <= i < v.len() ==> v[i] != key,
        },
// END SPEC
{
    None // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep a half-open window [lo, hi) that must contain key if key is anywhere.
H2. Invariant: bounds, sortedness (restated), and "left of lo is < key, right of hi is > key".
    Sortedness carries the facts about v[mid] to the whole discarded half.
H3. invariant lo <= hi <= v.len(), <sortedness>,
        forall|i: int| 0 <= i < lo ==> v[i] < key, forall|i: int| hi <= i < v.len() ==> v[i] > key,
    with let mid = lo + (hi - lo) / 2;
*/

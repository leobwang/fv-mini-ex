// M44 | Longest plateau | 15-20 min | optimality spec (exists + forall), ghost witness, run invariant
// GOAL
//   Return the length of the longest block of equal adjacent elements. The spec demands both that
//   such a block exists (exists) and that no block is longer (forall).
//
// REFERENCE
//   let ghost mut bi: int = 0;   proof { bi = start as int; }   // ghost witness for the exists
//   invariant forall|i: int, len: int| is_run(v@, i, len) && i + len <= k ==> len <= best
//   start > 0 ==> v[start - 1] != v[start as int]    // the current run cannot extend left
//   for k in 1..n invariant ..., { ... }              // the loop variable k starts at 1
// NOTE: a run that ends at index k and starts before `start` would contain v[start-1], v[start].

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn is_run(s: Seq<i64>, i: int, len: int) -> bool {
    &&& 0 <= i
    &&& 1 <= len
    &&& i + len <= s.len()
    &&& forall|k: int| i <= k < i + len ==> s[k] == s[i]
}

fn longest_plateau(v: &Vec<i64>) -> (r: usize)
    requires v.len() > 0,
    ensures
        exists|i: int| is_run(v@, i, r as int),
        forall|i: int, len: int| is_run(v@, i, len) ==> len <= r,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One pass: track where the current run starts and the best length so far. Keep a ghost index
    bi where a run of length best starts, for the exists part.
H2. Invariant for optimality: every run that fits inside v[..k] is <= best. When k grows, the only
    new runs end at k; such a run cannot start before `start`, since v[start-1] != v[start].
H3. invariant n == v.len(), start < k <= n, 1 <= best <= k, k - start <= best,
      is_run(v@, bi, best as int),
      forall|i: int, len: int| is_run(v@, i, len) && i + len <= k ==> len <= best,
      forall|j: int| start <= j < k ==> v[j] == v[start as int],
      start > 0 ==> v[start - 1] != v[start as int],
    and at the end of the body prove the optimality invariant for k + 1 with assert forall,
    using assert(v[start - 1] == v[i] && v[start as int] == v[i]) when i < start.
*/

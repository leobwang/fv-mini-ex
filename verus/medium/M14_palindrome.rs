// M14 | Palindrome check | 10-15 min | two indices, <==>, assert forall [R17]
// GOAL
//   Return true exactly when v reads the same forwards and backwards.
//
// REFERENCE
//   while i < n / 2 invariant ..., decreases n / 2 - i, { ... return false; ... }
//   forall|k: int| 0 <= k < i ==> #[trigger] v[k] == v[n - 1 - k]   // pick v[k]: v[n-1-k] is not
//       // allowed as a trigger (arithmetic inside), and picking v[k] must be explicit here
//   assert forall|k: int| 0 <= k < n implies #[trigger] v[k] == v[n - 1 - k] by {
//       if k >= n / 2 { assert(v[n - 1 - k] == v[n - 1 - (n - 1 - k)]); }   // use the mirror
//   }
// NOTE: `n - 1 - i` on usize underflows unless i < n.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn is_palindrome(v: &Vec<u8>) -> (b: bool)
    ensures b <==> forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i] == v[v.len() - 1 - i],
// END SPEC
{
    false // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare v[i] with v[n-1-i] for i < n/2; return false on the first mismatch.
H2. Invariant: the first i outer pairs match. When the loop ends normally, the postcondition
    for an index k in the right half follows from the pair (n-1-k, k); the middle index of
    an odd-length Vec is its own mirror. Prove the forall with `assert forall ... by`.
H3. invariant n == v.len(), i <= n / 2, forall|k: int| 0 <= k < i ==> #[trigger] v[k] == v[n - 1 - k],
    after the loop: assert forall|k: int| 0 <= k < n implies #[trigger] v[k] == v[n - 1 - k] by
        { if k >= n / 2 { assert(v[n - 1 - k] == v[n - 1 - (n - 1 - k)]); } }  (+ middle case)
*/

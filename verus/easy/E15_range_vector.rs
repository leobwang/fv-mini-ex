// E15 | Range vector | 2-3 min | Vec::new, push, building a result
// GOAL
//   Build the Vec [0, 1, ..., n-1].
//
// REFERENCE
//   let mut v: Vec<usize> = Vec::new();     // empty: v@ == Seq::empty()
//   v.push(x);                              // v@ becomes old v@.push(x)
//   invariant v.len() == i,                 // describe the partial result in the loop invariant
//   v[j] == j                               // usize compared with int: both sides are lifted to int

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn range_vec(n: usize) -> (v: Vec<usize>)
    ensures
        v.len() == n,
        forall|i: int| 0 <= i < n ==> v[i] == i,
// END SPEC
{
    Vec::new() // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Push i in iteration i.
H2. The invariant mirrors the postcondition with n replaced by i.
H3. invariant v.len() == i, forall|j: int| 0 <= j < i ==> v[j] == j,
*/

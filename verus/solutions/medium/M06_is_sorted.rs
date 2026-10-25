// M06 | Is sorted | 5-10 min | <==>, pairwise invariant from adjacent checks [R08]
// GOAL
//   Return true exactly when v is sorted (every earlier element <= every later one).
//   Checking adjacent pairs is enough in the code; the proof must bridge to all pairs.
//
// REFERENCE
//   ensures b <==> forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
//   for i in 1..v.len() invariant P(i), { ... return false; ... }
//   forall|a: int, b: int| 0 <= a < b < i ==> v[a] <= v[b]     // "prefix v[0..i) is sorted"
//   To prove `!forall ...` give a counterexample: the terms v[i-1], v[i as int] must appear.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn is_sorted(v: &Vec<i64>) -> (b: bool)
    ensures b <==> forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
// END SPEC
{
    if v.len() == 0 {
        return true;
    }
    for i in 1..v.len()
        invariant
            forall|a: int, b: int| 0 <= a < b < i ==> v[a] <= v[b],
    {
        if v[i - 1] > v[i] {
            return false;
        }
    }
    true
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare v[i-1] with v[i] for each i >= 1; bail out with false on a descent.
H2. Invariant: the prefix v[0..i) is pairwise sorted. Adding v[i] keeps it sorted by transitivity
    through v[i-1]. Handle the empty Vec before the loop.
H3. invariant forall|a: int, b: int| 0 <= a < b < i ==> v[a] <= v[b],
*/

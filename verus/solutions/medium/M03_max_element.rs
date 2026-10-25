// M03 | Max element | 5-10 min | for, forall, exists, ghost witness [R05]
// GOAL
//   Return the maximum of a non-empty Vec: it is >= every element and equals some element.
//
// REFERENCE
//   for i in 1..v.len() invariant P(i), { ... }        // i is usable in the invariant
//   let ghost mut w: int = 0;                          // ghost witness index
//   proof { w = i as int; }                            // update ghost state in exec code
//   exists|k: int| 0 <= k < v.len() && v[k] == m       // proved by any term v[w] with v[w] == m

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn max_element(v: &Vec<i64>) -> (r: i64)
    requires v.len() > 0,
    ensures
        forall|i: int| 0 <= i < v.len() ==> v[i] <= r,
        exists|i: int| 0 <= i < v.len() && v[i] == r,
// END SPEC
{
    let mut m = v[0];
    let ghost mut w: int = 0;
    for i in 1..v.len()
        invariant
            0 <= w < v.len(),
            v[w] == m,
            forall|k: int| 0 <= k < i ==> v[k] <= m,
    {
        if v[i] > m {
            m = v[i];
            proof { w = i as int; }
        }
    }
    m
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start from m = v[0] and scan the rest.
H2. Two invariants: m bounds the prefix seen so far, and m is one of the elements (keep a ghost
    index w with v[w] == m so the `exists` has a witness).
H3. invariant 0 <= w < v.len(), v[w] == m, forall|k: int| 0 <= k < i ==> v[k] <= m,
*/

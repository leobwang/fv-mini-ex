// M33 | All distinct | 10-15 min | nested loops, two-index invariant, early return
// GOAL
//   Return true iff no two positions of v hold the same value. Quadratic nested loops are fine.
//
// REFERENCE
//   for i in 0..n invariant P(i), { for j in (i + 1)..n invariant Q(i, j), { ... } }
//   forall|p: int, q: int| 0 <= p < i && p < q < v.len() ==> v[p] != v[q]   // rows done so far
//   // The inner loop's invariant must restate what it needs from the outer one
//   // (loops only see their own invariant, not the facts before them).
//   return false;                       // early return out of both loops

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn all_distinct(v: &Vec<u64>) -> (b: bool)
    ensures b <==> (forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j]),
// END SPEC
{
    let n = v.len();
    for i in 0..n
        invariant
            n == v.len(),
            forall|p: int, q: int| 0 <= p < i && p < q < n ==> v[p] != v[q],
    {
        for j in (i + 1)..n
            invariant
                n == v.len(), i < n,
                forall|p: int, q: int| 0 <= p < i && p < q < n ==> v[p] != v[q],
                forall|q: int| i < q < j ==> v[i as int] != v[q],
        {
            if v[i] == v[j] {
                return false;
            }
        }
    }
    true
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare every pair (i, j) with i < j. When a pair matches, that pair is the witness for false.
H2. Outer invariant: every pair whose smaller index is < i is distinct. Inner invariant: v[i]
    differs from v[q] for i < q < j, plus a copy of the outer invariant.
H3. outer: forall|p: int, q: int| 0 <= p < i && p < q < n ==> v[p] != v[q]
    inner: the same, plus  i < n,  forall|q: int| i < q < j ==> v[i as int] != v[q]
*/

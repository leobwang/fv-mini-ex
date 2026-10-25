// E21 | Distinct among three | 1-3 min | Set, set![], len
// GOAL
//   Return how many distinct values are among a, b, c.
//
// REFERENCE
//   set![a, b]                  // finite Set literal (duplicates collapse)
//   s.contains(x), s.insert(x)  // membership, add one element
//   s.len()                     // cardinality (nat), defined for finite sets
//   Verus evaluates the size of small literal sets on its own once the case is known.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn distinct3(a: u64, b: u64, c: u64) -> (r: u64)
    ensures r == set![a, b, c].len(),
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three possible answers: 1, 2 or 3.
H2. All equal gives 1; exactly one equal pair (any of three) gives 2.
H3. if a == b && b == c { 1 } else if a == b || b == c || a == c { 2 } else { 3 }
*/

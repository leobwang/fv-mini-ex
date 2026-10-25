// E13 | All below a bound | 2-3 min | for loop, invariant, forall
// GOAL
//   Return whether every element of v is strictly below b.
//
// REFERENCE
//   forall|i: int| 0 <= i < v.len() ==> v[i] < b       // quantifier over a mathematical int
//   for i in 0..v.len()
//       invariant forall|j: int| 0 <= j < i ==> P(j),   // i is in scope; 0 <= i <= len is known
//   { ... }
//   return false;                                      // early return is fine inside loops

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn all_below(v: &Vec<u64>, b: u64) -> (r: bool)
    ensures r == (forall|i: int| 0 <= i < v.len() ==> v[i] < b),
// END SPEC
{
    false // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Scan left to right; stop as soon as an element is too big.
H2. The invariant records that the prefix v[0..i] is fine.
H3. invariant forall|j: int| 0 <= j < i ==> v[j] < b,
*/

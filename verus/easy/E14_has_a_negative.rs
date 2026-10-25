// E14 | Has a negative | 1-3 min | exists, witness
// GOAL
//   Return whether v contains a negative element.
//
// REFERENCE
//   exists|i: int| 0 <= i < v.len() && v[i] < 0      // note: `&&` under exists, `==>` under forall
//   To prove an exists, the solver needs a witness term: returning right after
//   testing v[i] puts v[i] in front of it.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn has_neg(v: &Vec<i64>) -> (r: bool)
    ensures r == (exists|i: int| 0 <= i < v.len() && v[i] < 0),
// END SPEC
{
    false // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Same shape as E13, with the roles of true/false swapped.
H2. Returning false needs "no negative so far" as an invariant; returning true needs a witness.
H3. invariant forall|j: int| 0 <= j < i ==> v[j] >= 0,
*/

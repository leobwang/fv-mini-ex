// E06 | Sign | 1-2 min | match, guards, ==>
// GOAL
//   Return 1, 0 or -1 according to the sign of x, using a match.
//
// REFERENCE
//   match x { 0 => a, y if y > 0 => b, _ => c }   // literal, guarded and wildcard arms
//   ensures P ==> Q,                              // implication (spec only); binds looser than &&
//   -1i8                                          // typed literal

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn sign(x: i64) -> (r: i8)
    ensures
        x > 0 ==> r == 1,
        x == 0 ==> r == 0,
        x < 0 ==> r == -1,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three cases, three arms.
H2. A guard `y if y > 0` separates positive values from the wildcard.
H3. match x { 0 => 0, y if y > 0 => 1, _ => -1 }
*/

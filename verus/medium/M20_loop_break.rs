// M20 | First zero with loop/break | 5-10 min | loop, break, invariant_except_break, loop ensures
// GOAL
//   v is known to contain a 0. Find the first one using `loop` + `break` (while/for are banned).
//
// REFERENCE
//   loop
//       invariant_except_break P,   // holds at the top of every iteration, NOT after a break
//       invariant Q,                // holds always, including right after the loop
//       ensures R,                  // what you know after `break`: proved at each break
//       decreases e,
//   { if done { break; } ... }
// BANNED: while, for

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn first_zero(v: &Vec<u64>) -> (r: usize)
    requires exists|i: int| 0 <= i < v.len() && v[i] == 0,
    ensures
        r < v.len(),
        v[r as int] == 0,
        forall|j: int| 0 <= j < r ==> v[j] != 0,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The loop runs while v[i] != 0; why can i never run off the end? Because a zero lies ahead.
H2. invariant_except_break: i < v.len() and "some zero at index >= i". invariant: no zero
    before i. ensures: i is in range and v[i] == 0 (true exactly at the break).
H3. invariant_except_break i < v.len(), exists|k: int| i <= k < v.len() && v[k] == 0,
    invariant forall|j: int| 0 <= j < i ==> v[j] != 0,
    ensures i < v.len(), v[i as int] == 0,  decreases v.len() - i,
*/

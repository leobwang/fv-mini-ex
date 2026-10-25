// M02 | Linear search | 5-10 min | Option, while, early return, forall [R04]
// GOAL
//   Return the index of the FIRST occurrence of key in v, or None if key does not occur.
//
// REFERENCE
//   ensures match r { Some(i) => P(i), None => Q, },   // case split on the result in a contract
//   return Some(i);                                     // early exit from inside a loop
//   while i < v.len() invariant i <= v.len(), forall|j: int| 0 <= j < i ==> v[j] != key,
//       decreases v.len() - i,
//   v[i as int]       // in specs, index a Vec with an int; exec code uses v[i] with i: usize

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn linear_search(v: &Vec<i64>, key: i64) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < v.len() && v[i as int] == key
                && forall|j: int| 0 <= j < i ==> v[j] != key,
            None => forall|j: int| 0 <= j < v.len() ==> v[j] != key,
        },
// END SPEC
{
    None // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Scan left to right; return as soon as you see key.
H2. The invariant records what you learned so far: no key in the prefix v[0..i).
H3. invariant i <= v.len(), forall|j: int| 0 <= j < i ==> v[j] != key,
*/

// M28 | Last occurrence | 5-10 min | backward scan, usize vs int, underflow
// GOAL
//   Return the index of the LAST occurrence of key, or None if key does not occur.
//   Scan from the right end down to index 0.
//
// REFERENCE
//   let mut i: usize = v.len();  while i > 0 ... decreases i, { i = i - 1; ... }
//   v[i as int]                         // spec indexing takes int; exec indexing takes usize
//   forall|j: int| i <= j < v.len() ==> v[j] != key   // `i` (usize) is widened to int here
//   return Some(i);                     // early return from inside a loop
// NOTE: `i - 1` on a usize is an underflow error when i == 0. Decrement only after testing i > 0.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn last_index(v: &Vec<i64>, key: i64) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < v.len() && v[i as int] == key
                && forall|j: int| i < j < v.len() ==> v[j] != key,
            None => forall|j: int| 0 <= j < v.len() ==> v[j] != key,
        },
// END SPEC
{
    let mut i: usize = v.len();
    while i > 0
        invariant
            i <= v.len(),
            forall|j: int| i <= j < v.len() ==> v[j] != key,
        decreases i,
    {
        i = i - 1;
        if v[i] == key {
            return Some(i);
        }
    }
    None
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start with i = v.len() (one past the end) so that the "already scanned" region v[i..] is empty.
H2. Loop while i > 0: first decrement, then look at v[i]. Everything at index >= i (after the
    decrement, everything strictly right of the current index) is known to differ from key.
H3. while i > 0
        invariant i <= v.len(), forall|j: int| i <= j < v.len() ==> v[j] != key,
        decreases i,
    { i = i - 1; if v[i] == key { return Some(i); } }
*/

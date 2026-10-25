// E41 | Rotate last to front | 1-3 min | Vec pop, insert, unwrap
// GOAL
//   Move the last element of a non-empty Vec to the front, in place.
//
// REFERENCE
//   v.pop()            // Option<T>: Some(last) and v@ == old v@.drop_last(), or None if empty
//   o.unwrap()         // requires o is Some
//   v.insert(i, x)     // requires i <= v.len(); v@ == old v@.insert(i, x)
//   s.drop_last(), s.last(), seq![x] + s

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn rotate_right(v: &mut Vec<u64>)
    requires v.len() > 0,
    ensures final(v)@ == seq![old(v)@.last()] + old(v)@.drop_last(),
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two Vec methods do all the work.
H2. pop gives you the last element; insert at index 0 puts it in front.
H3. let x = v.pop().unwrap(); v.insert(0, x);
*/

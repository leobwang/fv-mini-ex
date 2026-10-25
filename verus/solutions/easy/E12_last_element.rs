// E12 | Last element | 1-2 min | Vec, v.len(), v[i], v@ view
// GOAL
//   Return the last element of a non-empty Vec.
//
// REFERENCE
//   fn f(v: &Vec<i64>)        // borrowed Vec
//   v.len(), v[i]             // exec: usize length, bounds-checked index (Verus proves i < v.len())
//   v@                        // spec: the Vec's view, a mathematical Seq<i64>
//   v@.len(), v@[i]           // spec length (nat) and element (index is an int)
//   In specs, v.len() and v[i] are shorthands for v@.len() and v@[i].

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn last(v: &Vec<i64>) -> (r: i64)
    requires v.len() > 0,
    ensures r == v@[v@.len() - 1],
// END SPEC
{
    v[v.len() - 1]
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The last index is v.len() - 1.
H2. The subtraction cannot underflow because of the requires clause.
H3. v[v.len() - 1]
*/

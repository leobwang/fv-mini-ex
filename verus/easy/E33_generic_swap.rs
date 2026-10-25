// E33 | Generic swap | 1-3 min | generics, T: Copy
// GOAL
//   Swap positions i and j of a Vec<T>, for any copyable T.
//
// REFERENCE
//   fn f<T: Copy>(v: &mut Vec<T>)    // generic exec fn; specs work the same for any T
//   let a = v[i];                     // reading copies the element (T: Copy)
//   v.set(i, b);                      // v@ becomes v@.update(i as int, b)
//   s.update(k, x)                    // spec: Seq with position k replaced

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn swap_elems<T: Copy>(v: &mut Vec<T>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        final(v)@ == old(v)@.update(i as int, old(v)[j as int]).update(j as int, old(v)[i as int]),
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read both elements before writing either.
H2. The order of the two writes matches the order of the two updates in the spec (matters when i == j? no).
H3. let a = v[i]; let b = v[j]; v.set(i, b); v.set(j, a);
*/

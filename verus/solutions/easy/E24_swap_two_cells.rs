// E24 | Swap two cells | 1-2 min | &mut, old, final
// GOAL
//   Swap the values behind two mutable references.
//
// REFERENCE
//   fn f(a: &mut u64)  requires *a < 10,   // in requires, *a is the value on entry
//       ensures *final(a) == *old(a) + 1,   // in ensures: old(a) = entry, final(a) = exit
//   { *a = *a + 1; }                        // in the body, *a is the current value
//   Bare *a in ensures is an error: always say old or final.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn swap(a: &mut u64, b: &mut u64)
    ensures
        *final(a) == *old(b),
        *final(b) == *old(a),
// END SPEC
{
    let t = *a;
    *a = *b;
    *b = t;
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Plain Rust works; the point is reading the old/final spec.
H2. Save one value in a temporary.
H3. let t = *a; *a = *b; *b = t;
*/

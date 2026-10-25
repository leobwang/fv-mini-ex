// E44 | Narrowing casts | 1-3 min | exec as casts, value known only when it fits
// GOAL
//   low_byte: keep the low 8 bits. to_u8: convert only when the value fits.
//
// REFERENCE
//   y as u8                 // exec narrowing cast: Verus knows its value only if y fits in u8
//   (x % 256) as u8         // so reduce into range first; then the cast is exact
//   x as u64                // widening casts are always exact
//   Some(v), None           // Option results, as in E20

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn low_byte(x: u32) -> (r: u8)
    ensures r == x % 256,
// END SPEC
{
    0 // TODO
}

// BEGIN SPEC
fn to_u8(x: u32) -> (r: Option<u8>)
    ensures
        r is Some <==> x < 256,
        r is Some ==> r->0 == x,
// END SPEC
{
    None // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A bare x as u8 compiles, but the postcondition fails: the solver doesn't know the truncated value.
H2. Make the value fit before casting: by reducing it (low_byte) or by testing it (to_u8).
H3. low_byte: (x % 256) as u8    to_u8: if x < 256 { Some(x as u8) } else { None }
*/

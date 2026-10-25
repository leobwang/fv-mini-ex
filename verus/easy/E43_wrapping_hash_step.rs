// E43 | Wrapping hash step | 1-3 min | wrapping_mul, wrapping_add
// GOAL
//   One step of a 32-bit multiplicative hash, h * 31 + c modulo 2^32, without overflow errors.
//
// REFERENCE
//   a.wrapping_mul(b), a.wrapping_add(b)   // ensures: result == (a op b) mod 2^bits
//   c as u32                               // widening cast (always exact)
//   0x1_0000_0000                          // 2^32 as a literal (an int in specs)
//   In specs, h as int * 31 is an exact mathematical product.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn hash_step(h: u32, c: u8) -> (r: u32)
    ensures r == ((h as int * 31) % 0x1_0000_0000 + c as int) % 0x1_0000_0000,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. h * 31 overflows u32 in general; the spec asks for the wrapped value.
H2. Rust's wrapping operations have exactly this spec in vstd.
H3. h.wrapping_mul(31).wrapping_add(c as u32)
*/

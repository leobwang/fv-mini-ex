// E29 | Bit tricks as arithmetic | 1-2 min | by (bit_vector)
// GOAL
//   Prove that masking the low bit is % 2 and shifting right by one is / 2.
//
// REFERENCE
//   assert(x & 1 == x % 2) by (bit_vector);    // decided by the bit-vector solver
//   assert(P) by (bit_vector) requires Q;      // with hypotheses (only Q is visible inside)
//   Operands must be fixed-width (u8..u64); no int, nat or spec function calls inside.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
proof fn bits_are_arith(x: u64)
    ensures
        x & 1 == x % 2,
        x >> 1 == x / 2,
// END SPEC
{
    assert(x & 1 == x % 2) by (bit_vector);
    assert(x >> 1 == x / 2) by (bit_vector);
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The default solver does not relate &, >> to %, /.
H2. One bit_vector assertion per ensures clause.
H3. assert(x & 1 == x % 2) by (bit_vector); assert(x >> 1 == x / 2) by (bit_vector);
*/

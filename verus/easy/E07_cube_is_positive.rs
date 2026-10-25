// E07 | Cube is positive | 1-3 min | proof fn, lemma call
// GOAL
//   Prove that x * x * x > 0 for x > 0, using the provided lemma_mul_pos.
//
// REFERENCE
//   proof fn lemma(x: int) requires P, ensures Q, { ... }   // ghost code, erased at runtime
//   lemma_mul_pos(a, b);       // inside a proof: checks requires, then adds ensures as a fact
//   x * y * z  ==  (x * y) * z  // left-associative
//   The solver does not multiply variables on its own (nonlinear); feed it lemma facts.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
proof fn lemma_mul_pos(x: int, y: int)
    requires x > 0, y > 0,
    ensures x * y > 0,
{
    // Provided. (This proof style is the subject of E16.)
    assert(x * y > 0) by (nonlinear_arith) requires x > 0, y > 0;
}

proof fn cube_pos(x: int)
    requires x > 0,
    ensures x * x * x > 0,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. x * x * x is (x * x) * x: a product of two positive things, if x * x is positive.
H2. Call the lemma twice, the second time with x * x as its first argument.
H3. lemma_mul_pos(x, x); lemma_mul_pos(x * x, x);
*/

// E08 | Powers of two | 2-3 min | recursive spec fn, decreases, nat subtraction
// GOAL
//   Define pow2(n) = 2^n as a recursive spec fn. pow2_facts pins down its meaning
//   (its empty proof goes through once pow2 is right).
//
// REFERENCE
//   spec fn f(n: nat) -> nat
//       decreases n,                        // termination measure: required for recursion
//   { if n == 0 { 0 } else { f((n - 1) as nat) } }
//   n - 1 has type int; `(n - 1) as nat` casts back (fine when n > 0)
// NOTE: `decreases` goes between the signature and the body, i.e. just below the frozen region.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
// END SPEC
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

// BEGIN SPEC
proof fn pow2_facts(n: nat)
    ensures
        pow2(0) == 1,
        n > 0 ==> pow2(n) == 2 * pow2((n - 1) as nat),
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Base case n == 0, recursive case n > 0.
H2. Without `decreases n,` Verus rejects the recursive call.
H3. decreases n, { if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) } }
*/

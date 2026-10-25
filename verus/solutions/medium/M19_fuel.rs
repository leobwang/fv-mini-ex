// M19 | Fuel | 5 min | reveal_with_fuel
// GOAL
//   Recursive spec fns unfold only one level per use ("fuel 1"). Prove three facts that need
//   several unfoldings, using reveal_with_fuel instead of long chains of asserts.
//
// REFERENCE
//   reveal_with_fuel(pow2, 4);     // let Verus unfold pow2 up to 4 levels in this proof
//   (n + 3 - 1) as nat             // what one unfolding of pow2(n + 3) produces: Verus
//                                  // normalizes it to n + 2, so the chain keeps going
// BANNED: compute

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

spec fn fib(n: nat) -> nat
    decreases n,
{
    if n < 2 { n } else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

proof fn pow2_plus3(n: nat)
    ensures pow2(n + 3) == 8 * pow2(n),
// END SPEC
{
    reveal_with_fuel(pow2, 4);
}

// BEGIN SPEC
proof fn fib_plus4(n: nat)
    ensures fib(n + 4) == 3 * fib(n + 1) + 2 * fib(n),
// END SPEC
{
    reveal_with_fuel(fib, 4);
}

// BEGIN SPEC
proof fn pow2_12()
    ensures pow2(12) == 4096,
// END SPEC
{
    reveal_with_fuel(pow2, 13);
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Count how many unfoldings each goal needs before it becomes plain arithmetic.
H2. pow2(n + 3) -> pow2(n + 2) -> pow2(n + 1) -> pow2(n): three steps; fib(n + 4) down to fib(n + 1)
    and fib(n) takes three levels too; pow2(12) down to pow2(0) takes twelve plus the base.
    Give a little more fuel than the count if in doubt.
H3. reveal_with_fuel(pow2, 4);   reveal_with_fuel(fib, 4);   reveal_with_fuel(pow2, 13);
*/

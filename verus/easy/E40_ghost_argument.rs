// E40 | Ghost argument | 2-3 min | Ghost<T> parameters
// GOAL
//   Implement double_pow, which takes the exponent only as a ghost argument,
//   then use it twice in quad.
//
// REFERENCE
//   fn f(x: u64, Ghost(k): Ghost<nat>)   // ghost parameter: exists only for specs, erased at runtime
//   f(7, Ghost(3))                        // caller wraps a spec value in Ghost(..)
//   Ghost(k + 1)                          // the argument of Ghost(..) is spec code
//   let g: Ghost<int> = Ghost(5);  g@     // @ unwraps a Ghost value

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

fn double_pow(x: u64, Ghost(k): Ghost<nat>) -> (r: u64)
    requires
        x == pow2(k),
        x <= 0x4000_0000_0000_0000,
    ensures r == pow2(k + 1),
// END SPEC
{
    0 // TODO
}

// BEGIN SPEC
fn quad(x: u64, Ghost(k): Ghost<nat>) -> (r: u64)
    requires
        x == pow2(k),
        x <= 0x2000_0000_0000_0000,
    ensures r == pow2(k + 2),
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. double_pow is one multiplication; the ghost k only appears in the contract.
H2. In quad, the second call needs the exponent of y, which is k + 1.
H3. let y = double_pow(x, Ghost(k)); double_pow(y, Ghost(k + 1))
*/

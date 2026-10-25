// E11 | Remainder by subtraction | 2-3 min | while, invariant, decreases
// GOAL
//   Compute rem(n, d) with a while loop that repeatedly subtracts d.
//
// REFERENCE
//   while cond
//       invariant I1, I2,        // holds on entry and after every iteration
//       decreases e,             // e >= 0 and strictly smaller after each iteration
//   { ... }
//   After the loop Verus knows only the invariants and !cond.
//   The loop body sees ONLY the invariants, not the function's requires: restate what you need.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn rem(n: nat, d: nat) -> nat
    decreases n,
{
    if d == 0 || n < d { n } else { rem((n - d) as nat, d) }
}

fn rem_loop(n: u64, d: u64) -> (r: u64)
    requires d > 0,
    ensures r == rem(n as nat, d as nat),
// END SPEC
{
    let mut r = n;
    while r >= d
        invariant
            d > 0,  // WHY: without it, `decreases r` cannot be proved inside the loop
            rem(r as nat, d as nat) == rem(n as nat, d as nat),
        decreases r,
    {
        r = r - d;
    }
    r
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep a mutable r, starting at n, and subtract d while r >= d.
H2. The invariant says the answer has not changed: rem(r, d) == rem(n, d).
H3. invariant d > 0, rem(r as nat, d as nat) == rem(n as nat, d as nat), decreases r,
*/

// M08 | Fibonacci, iterative | 15-20 min | recursive spec, monotonicity lemma, overflow [R10]
// GOAL
//   Compute fib(n) with a loop. The precondition says only that the FINAL answer fits in u64,
//   so you must prove every intermediate value also fits (fib is monotone).
//
// REFERENCE
//   proof fn lemma(i: nat, j: nat) requires i <= j ensures f(i) <= f(j) decreases j - i { .. }
//   proof { lemma_fib_mono((i + 1) as nat, n as nat); }   // call a lemma from exec code
//   let c = a + b;            // Verus must see c <= u64::MAX here: a lemma call supplies it
//   (n - 1) as nat            // nat subtraction in specs needs a cast back to nat
// NOTE: a loop that computes fib(i + 2) one step "ahead" can overflow on the last iteration.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn fib(n: nat) -> nat
    decreases n,
{
    if n < 2 { n } else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

fn fib_iter(n: u64) -> (r: u64)
    requires fib(n as nat) <= u64::MAX,
    ensures r == fib(n as nat),
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep (a, b) = (fib(i-1), fib(i)) and stop when i == n, so you never compute past fib(n).
H2. Prove a helper lemma fib(i) <= fib(j) for i <= j (first the one-step version
    fib(k) <= fib(k+1), then induction on j - i). Call it before `a + b` in the loop.
H3. proof fn lemma_fib_mono(i: nat, j: nat) requires i <= j ensures fib(i) <= fib(j) decreases j - i
    loop invariant 1 <= i <= n, fib(n as nat) <= u64::MAX, a == fib((i - 1) as nat), b == fib(i as nat),
    body: proof { lemma_fib_mono((i + 1) as nat, n as nat); }
*/

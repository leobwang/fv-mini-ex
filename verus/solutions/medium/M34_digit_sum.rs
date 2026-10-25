// M34 | Digit sum | 10-15 min | recursion on n / 10, loop invariant, overflow bound by lemma
// GOAL
//   Compute the decimal digit sum of n with a loop. The accumulator must never overflow, which
//   you justify with a small lemma of your own.
//
// REFERENCE
//   s + digit_sum(m as nat) == digit_sum(n as nat)    // invariant shape: done + todo == total
//   m % 10   m / 10                                    // division by a literal is linear arithmetic
//   proof fn my_lemma(n: nat) ensures ... decreases n, { if n > 0 { my_lemma(n / 10); } }
//   proof { my_lemma(n as nat); }                       // call it from exec code
// NOTE: `s + m % 10` needs a bound on s; digit_sum(n) <= n is true and easy to prove.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn digit_sum(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { n % 10 + digit_sum(n / 10) }
}

fn digit_sum_loop(n: u64) -> (r: u64)
    ensures r == digit_sum(n as nat),
// END SPEC
{
    proof { lemma_digit_sum_le(n as nat); }
    let mut m: u64 = n;
    let mut s: u64 = 0;
    while m > 0
        invariant
            s + digit_sum(m as nat) == digit_sum(n as nat),
            digit_sum(n as nat) <= n,
        decreases m,
    {
        s = s + m % 10;
        m = m / 10;
    }
    s
}

proof fn lemma_digit_sum_le(n: nat)
    ensures digit_sum(n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_digit_sum_le(n / 10);
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Peel the last digit each round: s += m % 10; m /= 10. The invariant says the digits already
    added plus the digit sum of what is left equal the answer.
H2. For overflow, s + m % 10 <= s + digit_sum(m) == digit_sum(n). So you need digit_sum(n) to fit:
    prove digit_sum(n) <= n by induction (n % 10 + n / 10 <= n).
H3. proof fn lemma_digit_sum_le(n: nat) ensures digit_sum(n) <= n decreases n
        { if n > 0 { lemma_digit_sum_le(n / 10); } }
    invariant  s + digit_sum(m as nat) == digit_sum(n as nat),  digit_sum(n as nat) <= n
*/

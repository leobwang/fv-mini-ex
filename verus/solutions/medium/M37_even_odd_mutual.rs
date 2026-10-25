// M37 | Even/odd mutual recursion | 8-12 min | mutually recursive spec fns, induction, lemma from exec
// GOAL
//   is_even and is_odd are defined in terms of each other. Prove they agree with % 2, then use
//   that to implement a constant-time exec check.
//
// REFERENCE
//   spec fn f(n: nat) -> bool decreases n { .. g((n - 1) as nat) .. }   // mutual recursion:
//   spec fn g(n: nat) -> bool decreases n { .. f((n - 1) as nat) .. }   // both share a measure
//   proof fn lemma(n: nat) ensures A(n), B(n), decreases n, { .. lemma((n - 1) as nat); .. }
//   proof { lemma(n as nat); }         // in exec code, before using the fact
// NOTE: prove both facts in ONE lemma: is_even's case needs is_odd's fact and vice versa.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn is_even(n: nat) -> bool
    decreases n,
{
    if n == 0 { true } else { is_odd((n - 1) as nat) }
}

spec fn is_odd(n: nat) -> bool
    decreases n,
{
    if n == 0 { false } else { is_even((n - 1) as nat) }
}

proof fn lemma_parity(n: nat)
    ensures
        is_even(n) <==> n % 2 == 0,
        is_odd(n) <==> n % 2 == 1,
// END SPEC
    decreases n,
{
    if n > 0 {
        lemma_parity((n - 1) as nat);
    }
}

// BEGIN SPEC
fn check_even(n: u64) -> (b: bool)
    ensures b == is_even(n as nat),
// END SPEC
{
    proof { lemma_parity(n as nat); }
    n % 2 == 0
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on n. For n > 0, is_even(n) is is_odd(n - 1), so you need the odd fact for n - 1.
H2. That is why the lemma states both facts: the induction hypothesis on n - 1 gives both.
    The exec function then computes n % 2 == 0 after calling the lemma.
H3. lemma_parity: decreases n,  { if n > 0 { lemma_parity((n - 1) as nat); } }
    check_even:   proof { lemma_parity(n as nat); }  n % 2 == 0
*/

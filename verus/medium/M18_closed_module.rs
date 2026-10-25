// M18 | Closed spec behind a module | 5-10 min | mod, pub closed spec fn, exported lemmas, as int
// GOAL
//   Module `parity` exports a closed predicate `even` plus three lemmas. Outside the module
//   the body of `even` is invisible (and cannot be revealed), so reason with the lemmas only.
//
// REFERENCE
//   mod m { use vstd::prelude::*; pub closed spec fn f(x: int) -> bool { .. } pub proof fn l() .. }
//   use parity::*;                 // bring the module's names into scope
//   even(2 * k as int)             // a nat argument needs an explicit `as int` for an int param
//   lemma_even_add2(2 * (k - 1));  // call an exported lemma; `k - 1` on nats is already an int
//   proof fn f(k: nat) ensures P(k) decreases k { if k > 0 { f((k - 1) as nat); .. } }
// NOTE: `reveal(even)` is rejected here: reveal is for opaque functions, not closed ones.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
mod parity {
    use vstd::prelude::*;

    pub closed spec fn even(n: int) -> bool {
        n % 2 == 0
    }

    pub proof fn lemma_even_zero()
        ensures even(0),
    {
    }

    pub proof fn lemma_even_add2(n: int)
        requires even(n),
        ensures even(n + 2),
    {
    }

    pub proof fn lemma_even_add(a: int, b: int)
        requires even(a), even(b),
        ensures even(a + b),
    {
    }
}

use parity::*;

proof fn lemma_even_double(k: nat)
    ensures even(2 * k as int),
    decreases k,
// END SPEC
{
}

// BEGIN SPEC
proof fn lemma_even_combo(a: nat, b: nat)
    ensures even((2 * a + 4 * b) as int),
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Without the body, `even(4)` is as mysterious as `f(4)`; only the lemmas tell you anything.
H2. lemma_even_double: induction on k. Base uses lemma_even_zero, step uses lemma_even_add2.
    lemma_even_combo: 2a + 4b = 2*a + 2*(2b); combine two doubles with lemma_even_add.
H3. step: lemma_even_double((k - 1) as nat); lemma_even_add2(2 * (k - 1));
    combo: lemma_even_double(a); lemma_even_double(2 * b);
           lemma_even_add(2 * a as int, 2 * (2 * b) as int);
*/

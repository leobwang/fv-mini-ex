// M11 | GCD by Euclid | 15-20 min | recursive spec, % reasoning, vstd div_mod lemmas [R13]
// GOAL
//   Compute gcd(a, b) with Euclid's loop, prove it equals the recursive spec, and prove the
//   result really divides both inputs.
//
// REFERENCE
//   use vstd::arithmetic::div_mod::*;
//   lemma_fundamental_div_mod(x, d);    // requires d != 0; ensures x == d * (x / d) + x % d
//   lemma_mod_multiples_basic(k, m);    // requires m > 0; ensures (k * m) % m == 0
//   proof fn lemma_gcd_divides(a: nat, b: nat) requires a > 0 ensures ... decreases b { .. }
//   assert(x == g * (p * q + s)) by (nonlinear_arith) requires x == g * p * q + g * s;
//   proof { lemma_gcd_divides(a as nat, b as nat); }      // call it from exec code

use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {

// BEGIN SPEC
spec fn gcd(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 { a } else { gcd(b, a % b) }
}

fn gcd_iter(a: u64, b: u64) -> (r: u64)
    requires a > 0,
    ensures
        r == gcd(a as nat, b as nat),
        r > 0,
        a % r == 0,
        b % r == 0,
// END SPEC
{
    let mut x = a;
    let mut y = b;
    while y != 0
        invariant
            x > 0,
            gcd(x as nat, y as nat) == gcd(a as nat, b as nat),
        decreases y,
    {
        let t = x % y;
        x = y;
        y = t;
    }
    proof { lemma_gcd_divides(a as nat, b as nat); }
    x
}

proof fn lemma_gcd_divides(a: nat, b: nat)
    requires a > 0,
    ensures
        gcd(a, b) > 0,
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
    decreases b,
{
    if b == 0 {
        lemma_mod_self_0(a as int);
    } else {
        let r = a % b;
        lemma_gcd_divides(b, r);
        let g = gcd(b, r);
        lemma_fundamental_div_mod(a as int, b as int);
        lemma_fundamental_div_mod(b as int, g as int);
        lemma_fundamental_div_mod(r as int, g as int);
        let k = (b / g) * (a / b) + r / g;
        assert(a == k * g) by (nonlinear_arith)
            requires a == b * (a / b) + r, b == g * (b / g), r == g * (r / g), k == (b / g) * (a / b) + r / g;
        lemma_mod_multiples_basic(k as int, g as int);
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The loop part is easy: the invariant is "gcd of the current pair == gcd of the inputs".
    The divisibility part needs its own lemma by induction following the spec's recursion.
H2. Lemma on (a, b), decreasing b. Base: gcd(a, 0) = a divides a and 0. Step: with
    g = gcd(b, a % b), the IH gives g | b and g | a % b; write a = b*(a/b) + a%b and factor g out.
H3. proof fn lemma_gcd_divides(a: nat, b: nat) requires a > 0
        ensures gcd(a, b) > 0, a % gcd(a, b) == 0, b % gcd(a, b) == 0 decreases b
    Step: k = (b/g)*(a/b) + (a%b)/g, prove a == k * g by (nonlinear_arith),
    then lemma_mod_multiples_basic(k, g). Loop invariant: x > 0, gcd(x, y) == gcd(a, b).
*/

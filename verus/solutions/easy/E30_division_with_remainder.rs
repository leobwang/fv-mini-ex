// E30 | Division with remainder | 2-3 min | vstd lemma, tuples
// GOAL
//   Return (a / b, a % b) and prove the division identity.
//
// REFERENCE
//   use vstd::arithmetic::div_mod::*;        // (already imported below)
//   lemma_fundamental_div_mod(x, d);         // requires d != 0; ensures x == d * (x / d) + x % d
//   fn f() -> (r: (u64, u64))  ..  ensures r.0 <= r.1   // tuple results: r.0, r.1
//   Lemma arguments are int: pass `a as int`.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {

// BEGIN SPEC
fn divmod(a: u64, b: u64) -> (r: (u64, u64))
    requires b > 0,
    ensures
        a == b * r.0 + r.1,
        r.1 < b,
// END SPEC
{
    proof {
        lemma_fundamental_div_mod(a as int, b as int);
    }
    (a / b, a % b)
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (a / b, a % b) is the right answer; the solver just doesn't know the identity.
H2. vstd proves it for you in lemma_fundamental_div_mod.
H3. proof { lemma_fundamental_div_mod(a as int, b as int); } (a / b, a % b)
*/

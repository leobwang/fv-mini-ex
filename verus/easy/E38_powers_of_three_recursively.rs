// E38 | Powers of three, recursively | 2-3 min | recursive exec fn, decreases
// GOAL
//   Decide is_pow3(n) with a recursive exec function mirroring the spec.
//
// REFERENCE
//   fn f(n: u64) -> (r: bool)
//       ensures r == g(n as nat),
//       decreases n,                 // exec recursion needs a measure too
//   { if n < 2 { .. } else { f(n / 2) } }
//   The recursive call's ensures is the "induction hypothesis" for n / 3.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn is_pow3(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        false
    } else if n == 1 {
        true
    } else if n % 3 != 0 {
        false
    } else {
        is_pow3(n / 3)
    }
}

fn check_pow3(n: u64) -> (r: bool)
    ensures r == is_pow3(n as nat),
// END SPEC
{
    false // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Follow the spec's case split literally.
H2. The recursive call needs `decreases n,` under the frozen region.
H3. decreases n, { if n == 0 { false } else if n == 1 { true } else if n % 3 != 0 { false } else { check_pow3(n / 3) } }
*/

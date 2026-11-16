// E01 | Absolute value | 1-3 min | verus!, fn, requires, ensures, overflow [R01]
// GOAL
//   Implement abs on i64. Note the precondition: -i64::MIN does not fit in i64.
//
// REFERENCE
//   use vstd::prelude::*;  verus! { ... }      // all verified code lives inside verus!
//   fn f(x: i64) -> (r: i64)                    // name the return value to use it in ensures
//       requires P,                              // comma-separated clauses
//       ensures Q, R,
//   { ... }
//   Arithmetic in specs is on mathematical `int`, so `-x` in ensures cannot overflow;
//   in executable code Verus proves every `-x`, `a + b`, ... stays in range.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn abs(x: i64) -> (r: i64)
    requires x > i64::MIN,
    ensures r >= 0, r == x || r == -x,
// END SPEC
{
    if x < 0 {-x} else {x}
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Branch on the sign of x; Rust `if` is an expression.
H2. `-x` overflows only for i64::MIN, which the precondition rules out.
H3. if x < 0 { -x } else { x }
*/

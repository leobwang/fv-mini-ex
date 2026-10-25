// E03 | Clamp | 1-2 min | pub open spec fn, as int
// GOAL
//   Clamp x into [lo, hi]. The spec is written as a spec function, clamp_spec.
//
// REFERENCE
//   pub open spec fn f(x: int) -> int { x + 1 }   // spec fn: math only, usable in specs, never run
//   ensures r == f(x as int),                     // spec fns take `int`: cast machine ints with `as int`
//   `open` makes the body visible outside this module (plain `spec fn` is fine within one file).
//   Exec code cannot call spec fns; it must compute the value itself.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
pub open spec fn clamp_spec(x: int, lo: int, hi: int) -> int {
    if x < lo { lo } else if x > hi { hi } else { x }
}

fn clamp(x: i64, lo: i64, hi: i64) -> (r: i64)
    requires lo <= hi,
    ensures r == clamp_spec(x as int, lo as int, hi as int),
// END SPEC
{
    if x < lo { lo } else if x > hi { hi } else { x }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Verus unfolds clamp_spec automatically; you only need to compute the same value.
H2. An if / else-if / else chain on i64 mirrors the spec exactly.
H3. if x < lo { lo } else if x > hi { hi } else { x }
*/

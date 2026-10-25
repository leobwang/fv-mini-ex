// E20 | Checked double subtraction | 2-3 min | Option, is, ->
// GOAL
//   Return Some(a - b - c) if it does not underflow, None otherwise.
//
// REFERENCE
//   Some(x), None                       // Option<T> as in Rust
//   r is Some, r is None                // spec: variant test
//   r->0                                // spec: payload of Some (field 0)
//   match r { Some(x) => .., None => .. }
// NOTE: in exec code, b + c can itself overflow.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn checked_sub2(a: u64, b: u64, c: u64) -> (r: Option<u64>)
    ensures
        r is None <==> a < b + c,
        r is Some ==> r->0 == a - b - c,
// END SPEC
{
    // WHY: test a >= b first so a - b is safe, instead of forming b + c.
    if a >= b && a - b >= c {
        Some(a - b - c)
    } else {
        None
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. In ensures, b + c is an int; in exec code it is a u64.
H2. Compare in two steps: a against b, then a - b against c.
H3. if a >= b && a - b >= c { Some(a - b - c) } else { None }
*/

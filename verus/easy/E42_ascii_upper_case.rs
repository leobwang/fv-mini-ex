// E42 | ASCII upper case | 1-2 min | u8, byte literals
// GOAL
//   Upper-case one ASCII byte; leave every other byte unchanged.
//
// REFERENCE
//   b'a', b'z', b'A'        // byte literals (u8), usable in exec code and specs
//   b'a' <= c <= b'z'       // chained comparison (spec); in exec write b'a' <= c && c <= b'z'
//   c - 32                  // exec u8 arithmetic is overflow-checked like any other

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn to_upper(c: u8) -> (r: u8)
    ensures
        b'a' <= c <= b'z' ==> r == c - 32,
        !(b'a' <= c <= b'z') ==> r == c,
// END SPEC
{
    0 // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two cases, as in the ensures.
H2. c - 32 cannot underflow when c >= b'a' (97).
H3. if b'a' <= c && c <= b'z' { c - 32 } else { c }
*/

// E23 | Accumulator commands | 2-3 min | enum, struct, match in spec
// GOAL
//   Apply one command to an accumulator, matching the spec function step.
//
// REFERENCE
//   enum Cmd { Add(u32), Reset }                 // data-carrying variants
//   struct Acc { val: u64 }                      // construct: Acc { val: 0 }, read: a.val
//   match c { Cmd::Add(k) => .., Cmd::Reset => .. }   // same syntax in spec and exec code
//   k as u64                                     // widen before mixing integer types in exec code

use vstd::prelude::*;

verus! {

// BEGIN SPEC
enum Cmd {
    Add(u32),
    Sub(u32),
    Reset,
}

struct Acc {
    val: u64,
}

spec fn step(c: Cmd, v: int) -> int {
    match c {
        Cmd::Add(k) => v + k,
        Cmd::Sub(k) => if v >= k { v - k } else { 0 },
        Cmd::Reset => 0,
    }
}

fn apply(a: Acc, c: Cmd) -> (r: Acc)
    requires a.val <= u32::MAX,
    ensures r.val == step(c, a.val as int),
// END SPEC
{
    Acc { val: 0 } // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One match arm per variant, each building a new Acc.
H2. The requires keeps Add from overflowing: u32::MAX + u32::MAX < u64::MAX.
H3. Cmd::Sub(k) => Acc { val: if a.val >= k as u64 { a.val - k as u64 } else { 0 } },
*/

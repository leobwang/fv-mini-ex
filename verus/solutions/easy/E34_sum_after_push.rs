// E34 | Sum after push | 1-3 min | drop_last, last, =~= inside arguments
// GOAL
//   Prove sum(s.push(x)) == sum(s) + x.
//
// REFERENCE
//   s.drop_last(), s.last()      // all but the last element; the last element (need s.len() > 0)
//   a =~= b                      // extensional equality: same length, same elements
//   Verus proves a top-level Seq equality element-wise by itself, but it will not rewrite
//   f(a) into f(b) until a == b is a known fact. Assert the equality of the arguments.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum(s.drop_last()) + s.last() }
}

proof fn sum_push(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x,
// END SPEC
{
    assert(s.push(x).drop_last() =~= s);
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold sum(s.push(x)) once: what is s.push(x).drop_last()?
H2. The solver needs to know that sequence is s itself.
H3. assert(s.push(x).drop_last() =~= s);
*/

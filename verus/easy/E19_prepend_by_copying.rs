// E19 | Prepend by copying | 2-3 min | Seq, seq![], +, subrange
// GOAL
//   Return a new Vec holding x followed by the elements of v.
//
// REFERENCE
//   seq![a, b]                  // Seq literal (spec)
//   s + t, s.push(x)            // concatenation, append one element
//   s.subrange(lo, hi)          // elements lo..hi (hi exclusive), indices are int
//   invariant r@ == seq![1u64] + v@.subrange(0, i as int),   // describe a partial copy
//   Equalities between Seqs are checked element-wise automatically.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn prepend(v: &Vec<u64>, x: u64) -> (r: Vec<u64>)
    ensures r@ == seq![x] + v@,
// END SPEC
{
    Vec::new() // TODO
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Push x, then copy v element by element.
H2. After the loop, v@.subrange(0, v.len()) is v@.
H3. invariant r@ == seq![x] + v@.subrange(0, i as int),
*/

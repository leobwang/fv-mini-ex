// E32 | All equal slice | 2-3 min | slices, two-variable forall, <==>
// GOAL
//   Return whether all elements of the slice are equal.
//
// REFERENCE
//   fn f(s: &[u64])                 // slice: s.len(), s[i] in exec; s@ is its Seq view
//   forall|i: int, j: int| P(i, j)  // several bound variables
//   ensures r <==> P,               // iff (spec); same as r == P for bools
//   forall|j: int| 0 <= j < i ==> #[trigger] s@[j] == s@[0]   // annotate if Verus can't pick one

use vstd::prelude::*;

verus! {

// BEGIN SPEC
fn all_equal(s: &[u64]) -> (r: bool)
    ensures r <==> (forall|i: int, j: int| 0 <= i < s@.len() && 0 <= j < s@.len() ==> s@[i] == s@[j]),
// END SPEC
{
    if s.len() == 0 {
        return true;
    }
    for i in 1..s.len()
        invariant
            s@.len() > 0,
            forall|j: int| 0 <= j < i ==> #[trigger] s@[j] == s@[0],
    {
        if s[i] != s[0] {
            return false;
        }
    }
    true
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare every element with s[0]; the empty slice is a special case.
H2. "Everything equals s[0]" implies "every pair is equal"; Verus does that step itself.
H3. invariant s@.len() > 0, forall|j: int| 0 <= j < i ==> #[trigger] s@[j] == s@[0],
*/

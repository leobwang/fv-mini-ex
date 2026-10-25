// E28 | Choose a witness | 1-3 min | choose
// GOAL
//   Define zero_index(s) as some index holding 0 (when one exists).
//
// REFERENCE
//   choose|i: int| P(i)        // spec: some i with P(i), if one exists (otherwise arbitrary)
//   If exists|i| P(i) is known, Verus knows P(choose|i| P(i)).
//   Like forall/exists, choose needs a trigger term, e.g. s[i].

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn zero_index(s: Seq<int>) -> int
// END SPEC
{
    0 // TODO
}

// BEGIN SPEC
proof fn zero_index_ok(s: Seq<int>)
    requires exists|i: int| 0 <= i < s.len() && s[i] == 0,
    ensures
        0 <= zero_index(s) < s.len(),
        s[zero_index(s)] == 0,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The body of zero_index is a single expression.
H2. Choose an index satisfying exactly the property in the requires.
H3. choose|i: int| 0 <= i < s.len() && s[i] == 0
*/

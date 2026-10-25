// E27 | Make the trigger fire | 1-3 min | #[trigger], trigger terms
// GOAL
//   Prove s[0] + s[1] > 0 from a quantified precondition whose trigger is is_pos(s[i]).
//
// REFERENCE
//   forall|i: int| 0 <= i < n ==> #[trigger] f(s[i])   // used only for terms of shape f(s[k])
//   A quantified fact is instantiated only when a term matching its trigger appears.
//   Mentioning such a term, e.g. assert(f(s[3]));, makes the instance available.
//   `verus --triggers` prints the triggers Verus picked when you don't annotate.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn is_pos(x: int) -> bool {
    x > 0
}

proof fn sum_two(s: Seq<int>)
    requires
        s.len() >= 2,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] is_pos(s[i]),
    ensures s[0] + s[1] > 0,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The goal mentions s[0] and s[1], but never is_pos(s[0]).
H2. Assert the two instances you need; each assert itself fires the trigger.
H3. assert(is_pos(s[0])); assert(is_pos(s[1]));
*/

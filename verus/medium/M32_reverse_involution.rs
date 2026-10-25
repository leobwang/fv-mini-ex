// M32 | Reverse is an involution | 15-20 min | recursive Seq spec, helper lemma, induction
// GOAL
//   rev is defined by peeling off the last element. Prove rev(rev(s)) == s.
//   You will need a helper lemma about rev of a sequence with a new FIRST element.
//
// REFERENCE
//   seq![x] + t                    // t with x in front;  s.push(x): x at the end
//   proof fn helper(x: int, t: Seq<int>) ensures rev(seq![x] + t) == rev(t).push(x) decreases t.len() { .. }
//   assert((seq![x] + t).drop_last() =~= seq![x] + t.drop_last());   // equality inside rev(...)
//   assert(s.drop_last().push(s.last()) =~= s);
// NOTE: helpers you add go outside the spec block; give each its own `decreases`.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn rev(s: Seq<int>) -> Seq<int>
    decreases s.len(),
{
    if s.len() == 0 { s } else { seq![s.last()] + rev(s.drop_last()) }
}

proof fn lemma_rev_rev(s: Seq<int>)
    ensures rev(rev(s)) == s,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. rev(rev(s)) for nonempty s is rev(seq![s.last()] + rev(s.drop_last())). You need to know
    what rev does to a sequence with a new first element.
H2. Helper: rev(seq![x] + t) == rev(t).push(x), by induction on t.len(). Then the main lemma is
    induction on s.len(): IH on s.drop_last(), the helper, and s.drop_last().push(s.last()) == s.
H3. proof fn lemma_rev_cons(x: int, t: Seq<int>)
        ensures rev(seq![x] + t) == rev(t).push(x), decreases t.len(),
    base:  assert(seq![x] + t =~= seq![x]); assert(seq![x].drop_last() =~= t); assert(rev(t) == t);
    step:  lemma_rev_cons(x, t.drop_last());
           assert((seq![x] + t).drop_last() =~= seq![x] + t.drop_last());
           plus the push/concat reassociation as an `=~=` assert.
    Main step: assert(rev(rev(s)) == rev(rev(s.drop_last())).push(s.last()));
*/

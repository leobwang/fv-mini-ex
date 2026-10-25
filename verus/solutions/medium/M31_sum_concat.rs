// M31 | Sum distributes over concat | 10 min | induction on Seq, =~= in arguments
// GOAL
//   Prove sum(a + b) == sum(a) + sum(b) for the drop_last-recursive sum.
//
// REFERENCE
//   proof fn lemma(a: Seq<int>, b: Seq<int>) ... decreases b.len(), { ... }  // induct on b
//   s.drop_last()   s.last()                 // s[..len-1] and s[len-1]
//   assert((a + b).drop_last() =~= a + b.drop_last());   // extensional equality of Seqs
//   // `=~=` is needed when the equality sits inside a function argument, as in sum(...).
// NOTE: write the `decreases` clause yourself, after the spec block.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum(s.drop_last()) + s.last() }
}

proof fn lemma_sum_concat(a: Seq<int>, b: Seq<int>)
    ensures sum(a + b) == sum(a) + sum(b),
// END SPEC
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_sum_concat(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
    }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. sum peels elements off the right end, so induct on b (the right operand).
H2. Base case: a + b is a. Step: (a + b) has the same last element as b, and its drop_last is
    a + b.drop_last(). Tell Verus both Seq equalities explicitly.
H3. decreases b.len(),
    if b.len() == 0 { assert(a + b =~= a); }
    else { lemma_sum_concat(a, b.drop_last());
           assert((a + b).drop_last() =~= a + b.drop_last()); }
*/

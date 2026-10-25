// M17 | Opaque sortedness | 5-10 min | #[verifier::opaque], reveal
// GOAL
//   `sorted` is opaque: Verus treats it as an uninterpreted predicate until you reveal it.
//   Prove the three contracts, revealing the definition exactly where it is needed.
//
// REFERENCE
//   #[verifier::opaque] spec fn p(x: int) -> bool { x > 0 }   // body hidden by default
//   reveal(p);                     // in proof code: the body is visible for the rest of this block
//   proof { reveal(sorted); }      // same thing from inside exec code
//   assert(P) by { reveal(p); }    // reveal only for one assertion
// NOTE: opaque keeps big quantified definitions from flooding the solver in unrelated proofs.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
#[verifier::opaque]
spec fn sorted(s: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn min_of_sorted(v: &Vec<i64>) -> (r: i64)
    requires v.len() > 0, sorted(v@),
    ensures forall|i: int| 0 <= i < v.len() ==> r <= v[i],
// END SPEC
{
    proof { reveal(sorted); }
    v[0]
}

// BEGIN SPEC
proof fn lemma_sorted_subrange(s: Seq<i64>, lo: int, hi: int)
    requires sorted(s), 0 <= lo <= hi <= s.len(),
    ensures sorted(s.subrange(lo, hi)),
// END SPEC
{
    reveal(sorted);
}

// BEGIN SPEC
fn push_sorted(v: &mut Vec<i64>, x: i64)
    requires sorted(v@), v.len() == 0 || v[v.len() - 1] <= x,
    ensures final(v)@ == old(v)@.push(x), sorted(final(v)@),
// END SPEC
{
    v.push(x);
    proof { reveal(sorted); }
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each of the three proofs is "obvious" once Verus can see what `sorted` means.
H2. Use reveal(sorted) in proof code; in exec code wrap it in proof { }.
H3. min_of_sorted: proof { reveal(sorted); } v[0]
    push_sorted: v.push(x); proof { reveal(sorted); }
*/

// M23 | Pointwise lemma over a Seq | 5-10 min | assert forall, implies, lemma per element
// GOAL
//   pow2 is monotone (lemma provided). Lift it to a whole sorted sequence: if s is sorted,
//   then mapping every element through pow2 keeps it sorted.
//
// REFERENCE
//   assert forall|i: int, j: int| 0 <= i < j < s.len() implies P(i, j) by {
//       lemma_pow2_mono(s[i], s[j]);      // inside: i, j are fixed, and the left side is a fact
//   }
//   // `implies` (not ==>) separates the hypothesis you get to assume from the goal P(i, j).
//   // After the block, `forall|i, j| 0 <= i < j < s.len() ==> P(i, j)` is known.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_pow2_mono(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b,
{
    if a < b {
        lemma_pow2_mono(a, (b - 1) as nat);
    }
}

spec fn sorted(s: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

proof fn lemma_pow2_sorted(s: Seq<nat>)
    requires sorted(s),
    ensures forall|i: int, j: int| 0 <= i < j < s.len() ==> pow2(s[i]) <= pow2(s[j]),
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The lemma handles one pair (a, b). The goal is a forall over all pairs.
H2. Prove the forall with `assert forall ... implies ... by { }` and call the lemma inside,
    where i and j are fixed and `0 <= i < j < s.len()` is assumed.
H3. assert forall|i: int, j: int| 0 <= i < j < s.len() implies pow2(s[i]) <= pow2(s[j]) by {
        lemma_pow2_mono(s[i], s[j]);
    }
*/

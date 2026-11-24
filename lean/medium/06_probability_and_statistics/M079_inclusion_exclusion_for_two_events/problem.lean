/- M079 | Inclusion–exclusion for two events | 10 min | measure_union, disjoint decomposition, set difference, ENNReal, mathlib
GOAL
  For events `A`, `B`: `μ (A ∪ B) + μ (A ∩ B) = μ A + μ B` (inclusion–exclusion, stated with `+` on
  both sides so that no truncated `ℝ≥0∞` subtraction appears). Build it from additivity on disjoint sets.
BANNED: measure_union_add_inter, measure_union_add_inter', measure_union_add_inter₀, measure_union_add_inter₀', measureReal_union_add_inter, measureReal_union_add_inter', measureReal_union_add_inter₀, measureReal_union_add_inter₀', restrict_union_add_inter, restrict_union_add_inter', restrict_union_add_inter₀, exact?, apply?, rw?, hint, try?

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M079

/- SKELETON · union_add_inter
  1. Fact 1, cut the union into disjoint pieces A and B \ A:
       have h1 : μ (A ∪ B) = μ A + μ (B \ A)
       proof: rewrite the union, then additivity                            R1, then R4 with
              arguments: the disjointness proof R2 and the measurability proof R3
  2. Fact 2, cut B by A, flipped so that `μ B` is its left side:
       have h2 : μ B = μ (B ∩ A) + μ (B \ A)                                R5 → R6
  3. Use both facts in the goal:                                            rw [h1, h2]
  4. Make the two intersections the same term (`A ∩ B` vs `B ∩ A`):         R7
  5. Both sides are now sums of the same three numbers:                     R8
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem union_add_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∪ B) + μ (A ∩ B) = μ A + μ B :=
-- END SPEC
  sorry

end M079

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Never subtract in `ℝ≥0∞`. Cut `A ∪ B` into the disjoint pieces `A` and `B \ A`, and cut `B` into
    `B ∩ A` and `B \ A`; then both sides are sums of the same three measures.
H2. Prove `μ (A ∪ B) = μ A + μ (B \ A)` (R1, R4 with R2, R3) and `μ B = μ (B ∩ A) + μ (B \ A)` (R5, R6)
    as two `have`s, `rw` with both, swap `A ∩ B` into `B ∩ A` (R7) and finish with `ring` (R8).
H3. `rw [← Set.union_sdiff_self, measure_union Set.disjoint_sdiff_right (hB.diff hA)]` proves the first;
    the second is `(measure_inter_add_sdiff B hA).symm`.
-/

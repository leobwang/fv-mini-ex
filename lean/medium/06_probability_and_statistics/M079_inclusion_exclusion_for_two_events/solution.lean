/- M079 | Inclusion–exclusion for two events | 10 min | measure_union, disjoint decomposition, set difference, ENNReal, mathlib
GOAL
  For events `A`, `B`: `μ (A ∪ B) + μ (A ∩ B) = μ A + μ B` (inclusion–exclusion, stated with `+` on
  both sides so that no truncated `ℝ≥0∞` subtraction appears). Build it from additivity on disjoint sets.

REFERENCE
  #check measure_union             -- Disjoint s₁ s₂ → MeasurableSet s₂ → μ (s₁ ∪ s₂) = μ s₁ + μ s₂
  #check measure_inter_add_sdiff   -- (s) → MeasurableSet t → μ (s ∩ t) + μ (s \ t) = μ s
  #check Set.union_sdiff_self      -- s ∪ t \ s = s ∪ t      (`\` binds tighter than `∪`)
  #check Set.disjoint_sdiff_right  -- Disjoint s (t \ s)
  example {Ω} [MeasurableSpace Ω] (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      MeasurableSet (B \ A) := hB.diff hA
  `B \ A` is set difference; `μ s : ℝ≥0∞`. `ring` can rearrange `+` and `*` in `ℝ≥0∞`.
BANNED: measure_union_add_inter, measure_union_add_inter', measure_union_add_inter₀, measure_union_add_inter₀', measureReal_union_add_inter, measureReal_union_add_inter', measureReal_union_add_inter₀, measureReal_union_add_inter₀', restrict_union_add_inter, restrict_union_add_inter', restrict_union_add_inter₀, exact?, apply?, rw?, hint, try?
-/
import Mathlib

namespace M079

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem union_add_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∪ B) + μ (A ∩ B) = μ A + μ B :=
-- END SPEC
  by
    have h1 : μ (A ∪ B) = μ A + μ (B \ A) := by
      rw [← Set.union_sdiff_self, measure_union Set.disjoint_sdiff_right (hB.diff hA)]
    have h2 : μ B = μ (B ∩ A) + μ (B \ A) := (measure_inter_add_sdiff B hA).symm
    rw [h1, h2, Set.inter_comm]
    ring

end M079

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Cut `A ∪ B` into the disjoint pieces `A` and `B \ A`, and cut `B` into `B ∩ A` and `B \ A`.
H2. Prove `μ (A ∪ B) = μ A + μ (B \ A)` and `μ B = μ (B ∩ A) + μ (B \ A)` as two `have`s, rewrite
    with both, then fix `B ∩ A` vs `A ∩ B` and finish with `ring`.
H3. `rw [← Set.union_sdiff_self, measure_union Set.disjoint_sdiff_right (hB.diff hA)]` proves the first;
    the second is `(measure_inter_add_sdiff B hA).symm`.
-/

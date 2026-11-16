/- E100 | Conditional probability | 3 min | cond, conditional probability notation, cond_apply, ENNReal inverse, mathlib
GOAL
  If `μ (A ∩ B) = μ A * μ B` and `μ A ≠ 0`, then conditioning on `A` does not change the probability
  of `B`: `μ[B | A] = μ B`.

REFERENCE
  `μ[B | A]` (from `open ProbabilityTheory`) is `cond μ A B`, the measure `μ` conditioned on `A`,
  evaluated at `B`. All values live in `ℝ≥0∞`, where `a⁻¹ * a = 1` needs `a ≠ 0` and `a ≠ ∞`.
  #check cond_apply              -- MeasurableSet s → ∀ μ t, μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)
  #check ENNReal.inv_mul_cancel  -- a ≠ 0 → a ≠ ∞ → a⁻¹ * a = 1
  #check measure_ne_top          -- (μ) [IsFiniteMeasure μ] (s) → μ s ≠ ∞
  #check mul_assoc               -- a * b * c = a * (b * c)
NOTE: `ring` and `field_simp` do not cancel `a⁻¹ * a` in `ℝ≥0∞`; rewrite with the lemma above.
-/
import Mathlib

namespace E100

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem cond_of_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hA0 : μ A ≠ 0)
    (h : μ (A ∩ B) = μ A * μ B) : μ[B | A] = μ B :=
-- END SPEC
  sorry

end E100

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold the conditional probability into `(μ A)⁻¹ * μ (A ∩ B)` and use `h`.
H2. You reach `(μ A)⁻¹ * (μ A * μ B)`. Reassociate so `(μ A)⁻¹ * μ A` appears, then cancel it.
H3. `rw [cond_apply hA, h, ← mul_assoc, ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A), one_mul]`.
-/

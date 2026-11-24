/- E100 | Conditional probability | 3 min | cond, conditional probability notation, cond_apply, ENNReal inverse, mathlib
GOAL
  If `μ (A ∩ B) = μ A * μ B` and `μ A ≠ 0`, then conditioning on `A` does not change the probability
  of `B`: `μ[B | A] = μ B`.

GUIDE
  Entries R1–R5: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E100

/- SKELETON · cond_of_indep
  One `rw` chain; every step rewrites the goal, which lives in `ENNReal` (no `ring` there).
  1. Unfold the conditional probability, given `hA`:                         R1
       goal: (μ A)⁻¹ * μ (A ∩ B) = μ B
  2. Substitute independence:                                                 rw [h]
       goal: (μ A)⁻¹ * (μ A * μ B) = μ B
  3. Regroup so that `(μ A)⁻¹ * μ A` is a subterm:                            R2
  4. Cancel it, with `hA0` and the finiteness fact `μ A ≠ ⊤`:                 R3 → R4
  5. Drop the `1 *`; `rw` then closes `μ B = μ B` by itself:                  R5
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem cond_of_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hA0 : μ A ≠ 0)
    (h : μ (A ∩ B) = μ A * μ B) : μ[B | A] = μ B :=
-- END SPEC
  by rw [cond_apply hA, h, ← mul_assoc, ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A), one_mul]

end E100

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `μ[B | A]` with `cond_apply` (R1): it becomes `(μ A)⁻¹ * μ (A ∩ B)`, and `μ (A ∩ B)` is the
    left side of `h`.
H2. After `rw [h]` you have `(μ A)⁻¹ * (μ A * μ B) = μ B`. Regroup with `← mul_assoc` (R2), cancel
    `(μ A)⁻¹ * μ A` with `ENNReal.inv_mul_cancel` (R4), then remove `1 *` with `one_mul` (R5).
H3. The cancellation needs `μ A ≠ 0` (that is `hA0`) and `μ A ≠ ⊤` (that is `measure_ne_top μ A`, R3):
    `rw [cond_apply hA, h, ← mul_assoc, ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A), one_mul]`.
-/

/- M082 | Complements of independent events | 10-15 min | IndepSet, ENNReal subtraction, measure algebra, mathlib
GOAL
  If the events `A` and `B` are independent under a probability measure `μ`, then so are `A` and `Bᶜ`
  (the complement of `B`).

REFERENCE
  `IndepSet A B μ`: the events `A`, `B` are independent, i.e. `μ (A ∩ B) = μ A * μ B` (see below).
  #check indepSet_iff_measure_inter_eq_mul  -- MeasurableSet s → MeasurableSet t → ∀ μ, IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t
  example {Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) (hA : MeasurableSet A)
      (hB : MeasurableSet B) := indepSet_iff_measure_inter_eq_mul hA hB.compl μ   -- pass `μ` explicitly
  #check measure_inter_add_sdiff   -- (s) → MeasurableSet t → μ (s ∩ t) + μ (s \ t) = μ s
  #check ENNReal.add_sub_cancel_left  -- a ≠ ∞ → a + b - a = b
  #check Set.sdiff_eq              -- s \ t = s ∩ tᶜ
  #check prob_compl_eq_one_sub     -- MeasurableSet s → μ sᶜ = 1 - μ s
  #check ENNReal.mul_sub           -- (0 < c → c < b → a ≠ ∞) → a * (b - c) = a * b - a * c
  #check measure_ne_top            -- (μ) [IsFiniteMeasure μ] (s) → μ s ≠ ∞
BANNED: indepSet_of_measurableSet, indep_of_indep_of_le_right, indep_of_indep_of_le_left
NOTE: `ℝ≥0∞` subtraction truncates at 0, so `ring` cannot distribute over `-`: every cancellation needs `≠ ∞`.
-/
import Mathlib

namespace M082

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem indep_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) (h : IndepSet A B μ) :
    IndepSet A Bᶜ μ :=
-- END SPEC
  sorry

end M082

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Turn both `IndepSet` statements into product equations; the goal becomes `μ (A ∩ Bᶜ) = μ A * μ Bᶜ`.
H2. Show `μ (A ∩ Bᶜ) = μ A - μ (A ∩ B)` (split `A` along `B`), then substitute `h` and
    `μ Bᶜ = 1 - μ B`, and distribute `μ A * (1 - μ B)`.
H3. `rw [← measure_inter_add_sdiff A hB, ENNReal.add_sub_cancel_left (measure_ne_top μ _), Set.sdiff_eq]`
    proves the `have`; then substitute `h1`, `h` and `prob_compl_eq_one_sub hB`, and distribute with
    `ENNReal.mul_sub` (its side goal is `μ A ≠ ∞`).
-/

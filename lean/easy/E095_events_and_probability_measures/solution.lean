/- E095 | Events and probability measures | 2-3 min | IsProbabilityMeasure, ENNReal, Measure.real, measure_mono, complement, mathlib
GOAL
  Basic facts about a probability measure `μ` on a sample space `Ω`: the complement rule, monotonicity
  and `μ B ≤ 1` for `μ : Measure Ω`, then the complement rule for the real-valued `μ.real`.

REFERENCE
  #check prob_compl_eq_one_sub      -- MeasurableSet s → μ sᶜ = 1 - μ s
  #check measure_mono               -- s ⊆ t → μ s ≤ μ t
  #check prob_le_one                -- μ s ≤ 1   (μ a probability measure)
  #check probReal_compl_eq_one_sub  -- MeasurableSet s → μ.real sᶜ = 1 - μ.real s
  `μ s : ℝ≥0∞` (`ENNReal`, the extended reals [0, ∞]); `μ.real s : ℝ` is `(μ s).toReal`.
  `[IsProbabilityMeasure μ]` is the instance `μ Set.univ = 1`; `Aᶜ` is the complement of `A`.
  `MeasurableSet A` says `A` is an event (a member of the σ-algebra `[MeasurableSpace Ω]`).
NOTE: subtraction in `ℝ≥0∞` truncates at 0 (like `ℕ`), so `ring` will not rearrange `1 - μ A` there.
-/
import Mathlib

namespace E095

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem events_basics {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hAB : A ⊆ B) :
    μ Aᶜ = 1 - μ A ∧ μ A ≤ μ B ∧ μ B ≤ 1 :=
-- END SPEC
  ⟨prob_compl_eq_one_sub hA, measure_mono hAB, prob_le_one⟩

-- BEGIN SPEC
theorem real_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) : μ.real A + μ.real Aᶜ = 1 :=
-- END SPEC
  by rw [probReal_compl_eq_one_sub hA]; ring

end E095

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each conjunct of `events_basics` is one library lemma from the card.
H2. Build the triple with `⟨_, _, _⟩`; the lemmas take the measurability or subset proof as argument.
    In `real_compl`, rewrite `μ.real Aᶜ` away, then the rest is real arithmetic.
H3. `⟨prob_compl_eq_one_sub hA, measure_mono hAB, prob_le_one⟩`;
    `rw [probReal_compl_eq_one_sub hA]; ring`.
-/

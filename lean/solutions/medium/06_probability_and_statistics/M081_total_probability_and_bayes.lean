/- M081 | Total probability and Bayes | 15 min | cond, partitions, measure_iUnion, simp_rw, ENNReal, mathlib
GOAL
  Law of total probability over a finite measurable partition `B : ι → Set Ω` of `Ω`:
  `μ A = ∑ i, μ[A | B i] * μ (B i)`. Then Bayes' formula for the posterior `μ[B j | A]`.

REFERENCE
  `μ[A | B]` (from `open ProbabilityTheory`) is `cond μ B A`, the probability of `A` given `B`.
  `Pairwise (Function.onFun Disjoint B)` says `Disjoint (B i) (B j)` whenever `i ≠ j`.
  #check cond_mul_eq_inter        -- MeasurableSet s → ∀ t μ [IsFiniteMeasure μ], μ[t | s] * μ s = μ (s ∩ t)
  #check cond_eq_inv_mul_cond_mul -- MeasurableSet s → MeasurableSet t → ∀ μ, μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t
  #check measure_iUnion           -- Pairwise (onFun Disjoint f) → (∀ i, MeasurableSet (f i)) → μ (⋃ i, f i) = ∑' i, μ (f i)
  #check tsum_fintype             -- ∑' b, f b = ∑ b, f b      (finite index type)
  #check Set.iUnion_inter         -- (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s
  example {α} (s t u : Set α) (h : Disjoint s t) : Disjoint (s ∩ u) (t ∩ u) :=
    h.mono Set.inter_subset_left Set.inter_subset_left
  `simp_rw [cond_mul_eq_inter (hmeas _)]` rewrites under the binder of `∑ i, …` (`rw` cannot).
  `conv_lhs => rw [h]` rewrites only the goal's left side (`rw [h]` hits every match); `Set.univ_inter`: `univ ∩ s = s`.
NOTE: values are in `ℝ≥0∞`; `a / b` there is `a * b⁻¹` (`div_eq_mul_inv`), and `ring` handles `⁻¹` as an atom.
-/
import Mathlib

namespace M081

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem total_probability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (hcover : ⋃ i, B i = Set.univ)
    (A : Set Ω) (hA : MeasurableSet A) :
    μ A = ∑ i, μ[A | B i] * μ (B i) :=
-- END SPEC
  by
    simp_rw [cond_mul_eq_inter (hmeas _)]
    have hA' : A = ⋃ i, B i ∩ A := by rw [← Set.iUnion_inter, hcover, Set.univ_inter]
    conv_lhs => rw [hA']
    rw [measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun i => (hmeas i).inter hA), tsum_fintype]

-- BEGIN SPEC
theorem bayes {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (hcover : ⋃ i, B i = Set.univ)
    (A : Set Ω) (hA : MeasurableSet A) (j : ι) :
    μ[B j | A] = μ[A | B j] * μ (B j) / ∑ i, μ[A | B i] * μ (B i) :=
-- END SPEC
  by
    rw [← total_probability μ B hmeas hdisj hcover A hA, cond_eq_inv_mul_cond_mul hA (hmeas j),
      div_eq_mul_inv]
    ring

end M081

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each term `μ[A | B i] * μ (B i)` is just `μ (B i ∩ A)`, and the sets `B i ∩ A` partition `A`.
H2. `simp_rw` the terms into `μ (B i ∩ A)`; show `A = ⋃ i, B i ∩ A` from `hcover`; apply countable
    additivity and turn `∑'` into `∑`. For Bayes, rewrite the denominator back to `μ A` first.
H3. `have : A = ⋃ i, B i ∩ A := by rw [← Set.iUnion_inter, hcover, Set.univ_inter]`, then
    `conv_lhs => rw [this]`; Bayes: `rw [← total_probability μ B hmeas hdisj hcover A hA, cond_eq_inv_mul_cond_mul hA (hmeas j), div_eq_mul_inv]; ring`.
-/

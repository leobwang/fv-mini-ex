/- H057 | Hoeffding's inequality | 45-75 min | Hoeffding's lemma, mgf of independent sums, Chernoff bound, optimisation, mathlib
GOAL
  Independent `X i` with values in `[a, b]` and mean `0`, `S = X 0 + … + X (n-1)`: `P(S ≥ ε) ≤ exp(-2ε² / (n (b-a)²))`.
  Bound each mgf by Hoeffding's lemma, multiply (independence), apply Chernoff, then choose the best `t`.

REFERENCE
  `mgf X μ t` is the moment generating function `μ[fun ω => Real.exp (t * X ω)]`;  `iIndepFun X μ`: the `X i` are mutually independent.
  #check ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero  -- Hoeffding's lemma: AEMeasurable X μ →
      -- (∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) → μ[X] = 0 → 0 < t → mgf X μ t ≤ exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2)
  #check iIndepFun.mgf_sum           -- iIndepFun X μ → (∀ i, Measurable (X i)) → ∀ s, mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t
  #check measure_ge_le_exp_mul_mgf   -- (ε) → 0 ≤ t → Integrable (fun ω => exp (t * X ω)) μ → μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t
  #check integrable_exp_mul_of_mem_Icc  -- AEMeasurable X μ → (∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) → Integrable (fun ω => exp (t * X ω)) μ
  #check Finset.prod_le_prod         -- (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ g i) → ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i  (`mgf_nonneg : 0 ≤ mgf X μ t`)
  #check Real.exp_nat_mul            -- exp (n * x) = exp x ^ n      (and `Real.exp_add : exp (x + y) = exp x * exp y`)
  #check Finset.measurable_sum       -- (s) → (∀ i ∈ s, Measurable (f i)) → Measurable fun a => ∑ i ∈ s, f i a
  example (x : ℝ) (h : 0 < x) : (‖x‖₊ : ℝ) = x := by rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos h]
  example (P : ℝ → Prop) (μ : MeasureTheory.Measure ℝ) (h : ∀ x, P x) : ∀ᵐ x ∂μ, P x := Filter.Eventually.of_forall h
BANNED: HasSubgaussianMGF, HasSubgaussianMGF_iff_kernel, measure_sum_ge_le_of_iIndepFun, measure_sum_range_ge_le_of_iIndepFun, sum_of_iIndepFun, hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero, hasSubgaussianMGF_of_mem_Icc, add_of_indepFun, measure_ge_le, measure_ge_le_exp_add, measure_sum_ge_le_of_hasCondSubgaussianMGF, sum_of_hasCondSubgaussianMGF, add_of_hasCondSubgaussianMGF, measureReal_le_le_exp
NOTE: Hoeffding's lemma is `protected`: write `ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero` in full even after `open ProbabilityTheory`.
-/
import Mathlib

namespace H057

open MeasureTheory ProbabilityTheory

-- MILESTONE (optional: change or delete)
theorem mgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ) (hab : a < b) (hmeas : Measurable X)
    (hbdd : ∀ ω, X ω ∈ Set.Icc a b) (hmean : μ[X] = 0) (t : ℝ) (ht : 0 < t) :
    mgf X μ t ≤ Real.exp (((b - a) / 2) ^ 2 * t ^ 2 / 2) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem mgf_sum_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[X i] = 0) (t : ℝ) (ht : 0 < t) :
    mgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ t
      ≤ Real.exp (n * (((b - a) / 2) ^ 2 * t ^ 2 / 2)) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem tail_le_for_all_t {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[X i] = 0) (ε t : ℝ) (ht : 0 < t) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-t * ε + n * (((b - a) / 2) ^ 2 * t ^ 2 / 2)) := by
  sorry

-- BEGIN SPEC
theorem hoeffding {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[X i] = 0) (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-2 * ε ^ 2 / (n * (b - a) ^ 2)) :=
-- END SPEC
  sorry

end H057

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `c = ((b - a) / 2)²`. Then `mgf (X i) t ≤ exp (c t² / 2)`, so `mgf S t ≤ exp (n c t² / 2)`, and Chernoff
    gives `P(S ≥ ε) ≤ exp (-t ε + n c t² / 2)` for every `t > 0`. Minimise the exponent over `t`.
H2. `mgf_le`: `convert` Hoeffding's lemma `using 3`, then turn `‖b - a‖₊` into `b - a`. `mgf_sum_le`: rewrite the
    function `fun ω => ∑ i ∈ range n, X i ω` as `∑ i ∈ range n, X i` (`funext ω; simp`), then `hindep.mgf_sum hmeas`,
    `Real.exp_nat_mul` and `Finset.prod_le_prod`. Chernoff's integrability: `S ω ∈ [n a, n b]`.
H3. The best choice is `t = ε / (n * ((b - a) / 2) ^ 2)` (positive by `positivity`). Main goal:
    `refine (tail_le_for_all_t μ n X a b hab hmeas hindep hbdd hmean ε _ ht).trans_eq ?_`, then `congr 1; field_simp; ring`.
    In `tail_le_for_all_t`: `calc` Chernoff, then `gcongr` with `mgf_sum_le`, then `(Real.exp_add _ _).symm`.
-/

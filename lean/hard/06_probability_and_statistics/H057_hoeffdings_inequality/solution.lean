/- H057 | Hoeffding's inequality | 45-75 min | Hoeffding's lemma, mgf of independent sums, Chernoff bound, optimisation, mathlib
GOAL
  Independent `X i` with values in `[a, b]` and mean `0`, `S = X 0 + … + X (n-1)`: `P(S ≥ ε) ≤ exp(-2ε² / (n (b-a)²))`.
  Bound each mgf by Hoeffding's lemma, multiply (independence), apply Chernoff, then choose the best `t`.

BANNED: HasSubgaussianMGF, HasSubgaussianMGF_iff_kernel, measure_sum_ge_le_of_iIndepFun, measure_sum_range_ge_le_of_iIndepFun, sum_of_iIndepFun, hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero, hasSubgaussianMGF_of_mem_Icc, add_of_indepFun, measure_ge_le, measure_ge_le_exp_add, measure_sum_ge_le_of_hasCondSubgaussianMGF, sum_of_hasCondSubgaussianMGF, add_of_hasCondSubgaussianMGF, measureReal_le_le_exp

GUIDE
  Entries R1–R29: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H057

open MeasureTheory ProbabilityTheory

/- SKELETON · mgf_le   (MILESTONE 1: used in `mgf_sum_le`, once per factor)
  1. Hoeffding's lemma as a hypothesis (full name: it is `protected`):              R3
       its arguments: `AEMeasurable X μ` from `hmeas` (R1), the a.s. bound from `hbdd` (R2),
       `hmean`, `ht`
       h : mgf X μ t ≤ Real.exp ((↑‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2)
  2. Match the goal against `h`, depth 3:                                         R4
       goal: `((b - a) / 2) ^ 2 * t ^ 2 = (↑‖b - a‖₊ / 2) ^ 2 * t ^ 2`
  3. Turn `↑‖b - a‖₊` into `b - a`; the side goal `0 < b - a` from `hab`:         R5 → R6 → R7 (R8)
-/
-- MILESTONE (optional: change or delete)
theorem mgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ) (hab : a < b) (hmeas : Measurable X)
    (hbdd : ∀ ω, X ω ∈ Set.Icc a b) (hmean : μ[X] = 0) (t : ℝ) (ht : 0 < t) :
    mgf X μ t ≤ Real.exp (((b - a) / 2) ^ 2 * t ^ 2 / 2) := by
  have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hmeas.aemeasurable
    (Filter.Eventually.of_forall hbdd) hmean ht
  convert h using 3
  rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (by linarith)]

/- SKELETON · mgf_sum_le   (MILESTONE 2: used in `tail_le_for_all_t`; uses `mgf_le`)
  1. `e : (fun ω => ∑ i ∈ Finset.range n, X i ω) = ∑ i ∈ Finset.range n, X i`:     `funext ω`, `simp` (R9)
  2. rw with `e`, then independence, then the power:                               R10, R11
       goal: `∏ i ∈ Finset.range n, mgf (X i) μ t ≤ Real.exp (((b - a) / 2) ^ 2 * t ^ 2 / 2) ^ n`
  3. `calc`:  `_ ≤ ∏ i ∈ Finset.range n, Real.exp (((b - a) / 2) ^ 2 * t ^ 2 / 2)`
                 R12: nonnegative factors by R13, factor bounds by MILESTONE `mgf_le`
              `_ = _`  by `simp`                                                    R14, R15
-/
-- MILESTONE (optional: change or delete)
theorem mgf_sum_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[X i] = 0) (t : ℝ) (ht : 0 < t) :
    mgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ t
      ≤ Real.exp (n * (((b - a) / 2) ^ 2 * t ^ 2 / 2)) := by
  have e : (fun ω => ∑ i ∈ Finset.range n, X i ω) = ∑ i ∈ Finset.range n, X i := by
    funext ω; simp
  rw [e, hindep.mgf_sum hmeas, Real.exp_nat_mul]
  calc ∏ i ∈ Finset.range n, mgf (X i) μ t
      ≤ ∏ i ∈ Finset.range n, Real.exp (((b - a) / 2) ^ 2 * t ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg)
          (fun i _ => mgf_le μ (X i) a b hab (hmeas i) (hbdd i) (hmean i) t ht)
    _ = _ := by simp

/- SKELETON · tail_le_for_all_t   (MILESTONE 3: used in `hoeffding`; uses `mgf_sum_le`)
  1. `hS : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range n, X i ω)) μ`:
       bounded variable, bounds named `(a := n * a) (b := n * b)`:                 R16
       measurability of the sum: R17 gives `Measurable`, R1 makes it `AEMeasurable`:  R17, R1
       a.s. bound from a pointwise bound (`intro ω` or `fun ω =>`), split the interval: R2, R18
         `↑n * a ≤ ∑ …`:  `calc` through `∑ i ∈ Finset.range n, a` (`simp`: R20, R15, R21),
                          then R19 with `(hbdd i ω).1` (R18)
         `∑ … ≤ ↑n * b`:  the same with `.2`
  2. `calc`, three steps:
       Chernoff with `hS`:                                                          R22 (R23 for `0 ≤ t`)
       `_ ≤ Real.exp (-t * ε) * Real.exp (n * …)`:  R24, then MILESTONE `mgf_sum_le`
       `_ = _`:  merge the exponentials                                             R25 (reversed)
-/
-- MILESTONE (optional: change or delete)
theorem tail_le_for_all_t {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[X i] = 0) (ε t : ℝ) (ht : 0 < t) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-t * ε + n * (((b - a) / 2) ^ 2 * t ^ 2 / 2)) := by
  have hS : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range n, X i ω)) μ := by
    refine integrable_exp_mul_of_mem_Icc (a := n * a) (b := n * b)
      (Finset.measurable_sum _ fun i _ => hmeas i).aemeasurable
      (Filter.Eventually.of_forall fun ω => ⟨?_, ?_⟩)
    · calc (n : ℝ) * a = ∑ i ∈ Finset.range n, a := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => (hbdd i ω).1
    · calc _ ≤ ∑ i ∈ Finset.range n, b := Finset.sum_le_sum fun i _ => (hbdd i ω).2
        _ = n * b := by simp
  calc μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-t * ε) * mgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ t :=
        measure_ge_le_exp_mul_mgf ε ht.le hS
    _ ≤ Real.exp (-t * ε) * Real.exp (n * (((b - a) / 2) ^ 2 * t ^ 2 / 2)) := by
        gcongr
        exact mgf_sum_le μ n X a b hab hmeas hindep hbdd hmean t ht
    _ = _ := (Real.exp_add _ _).symm

/- SKELETON · hoeffding
  Prove the three MILESTONES first, in order (`mgf_le` → `mgf_sum_le` → `tail_le_for_all_t`):
  step 3 uses `tail_le_for_all_t`, which uses the other two.
  1. Facts for the arithmetic: `0 < b - a` (R8), `0 < ((b - a) / 2) ^ 2` (R26)
  2. The optimal `t`: `ht : 0 < ε / (n * ((b - a) / 2) ^ 2)`                       R26
       why: the exponent `-t ε + n c t² / 2`, `c = ((b - a) / 2)²`, is least at `t = ε / (n c)`
  3. MILESTONE `tail_le_for_all_t` at that `t`, leaving an equation of bounds:     R27
       goal: `Real.exp (-(ε / (↑n * ((b - a) / 2) ^ 2)) * ε + …) = Real.exp (-2 * ε ^ 2 / (↑n * (b - a) ^ 2))`
  4. Equal exponents, clear denominators, finish:                                  R28, R29, `ring`
-/
-- BEGIN SPEC
theorem hoeffding {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b) (hmean : ∀ i, μ[X i] = 0) (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-2 * ε ^ 2 / (n * (b - a) ^ 2)) :=
-- END SPEC
  by
    have hba : 0 < b - a := by linarith
    have hc : 0 < ((b - a) / 2) ^ 2 := by positivity
    -- WHY: `t = ε / (n c)` minimises the exponent `-t ε + n c t² / 2`.
    have ht : 0 < ε / (n * ((b - a) / 2) ^ 2) := by positivity
    refine (tail_le_for_all_t μ n X a b hab hmeas hindep hbdd hmean ε _ ht).trans_eq ?_
    congr 1
    field_simp
    ring

end H057

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `c = ((b - a) / 2)²`. Then `mgf (X i) t ≤ exp (c t² / 2)` (Hoeffding's lemma, R3), so
    `mgf S t ≤ exp (n c t² / 2)` (independence, R10), and Chernoff (R22) gives `P(S ≥ ε) ≤ exp (-t ε + n c t² / 2)`
    for every `t > 0`. These are the three MILESTONES; `hoeffding` only chooses `t`.
H2. `mgf_le`: `have h :=` Hoeffding's lemma, then `convert h using 3` (R4) and turn `↑‖b - a‖₊` into `b - a`
    (R5–R7). `mgf_sum_le`: first `e : (fun ω => ∑ …, X i ω) = ∑ …, X i` (`funext ω; simp`), then rewrite to a
    product and compare factors with `Finset.prod_le_prod` (R12). `tail_le_for_all_t`: integrability from
    `S ω ∈ [n a, n b]` (R16), then a `calc`: Chernoff, `gcongr` with `mgf_sum_le`, merge the `exp`s.
    `hoeffding`: minimise `-t ε + n c t² / 2`: `t = ε / (n c)`.
H3. `convert h using 3; rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (by linarith)]`;
    `rw [e, hindep.mgf_sum hmeas, Real.exp_nat_mul]`;
    `refine integrable_exp_mul_of_mem_Icc (a := n * a) (b := n * b) (Finset.measurable_sum _ fun i _ => hmeas i).aemeasurable (Filter.Eventually.of_forall fun ω => ⟨?_, ?_⟩)`.
    Main goal: `have ht : 0 < ε / (n * ((b - a) / 2) ^ 2) := by positivity`, then
    `refine (tail_le_for_all_t μ n X a b hab hmeas hindep hbdd hmean ε _ ht).trans_eq ?_` and `congr 1; field_simp; ring`.
-/

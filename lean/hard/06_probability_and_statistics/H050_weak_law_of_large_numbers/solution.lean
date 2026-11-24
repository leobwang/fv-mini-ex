/- H050 | Weak law of large numbers | 1-1.5 h | TendstoInMeasure, Chebyshev, variance of sums, ENNReal limits, squeeze, mathlib
GOAL
  Pairwise independent `L²` variables `X i` with common mean `m` and `Var (X i) ≤ C`: the sample mean
  `X̄ₙ = (X 0 + … + X (n-1)) / n` converges to `m` in probability (`P(|X̄ₙ - m| ≥ ε) → 0` for every `ε > 0`).
  Bound `Var X̄ₙ ≤ C / n`, apply Chebyshev, then squeeze the probabilities (values in `ℝ≥0∞`) to `0`.

GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H050

open MeasureTheory ProbabilityTheory Filter Topology

/- SKELETON · sample_mean_mean   (milestone 1: E X̄ₙ = m)
  1. Pull `/ ↑n` out of the integral:                                        R1
  2. Swap the integral and the finite sum; each summand is integrable
     because it is L²:                                                       R3 (its argument by R2)
  3. Replace each `∫ X i` by `m` and sum the constants: goal `↑n * m / ↑n = m`: R4 (with hmean)
  4. Cancel `↑n` (hn gives `↑n ≠ 0`):                                        R5
-/
-- MILESTONE (optional: change or delete)
theorem sample_mean_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m : ℝ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (n : ℕ) (hn : 0 < n) :
    μ[fun ω => (∑ i ∈ Finset.range n, X i ω) / n] = m := by
  rw [integral_div, integral_finsetSum _ (fun i _ => (hL2 i).integrable one_le_two)]
  simp [hmean]
  field_simp

/- SKELETON · sample_mean_variance_le   (milestone 2: Var X̄ₙ ≤ C / n)
  1. Restate the sample mean in the shape the variance lemmas want:          R6 → R7 → R8
       e : (fun ω => (∑ i ∈ Finset.range n, X i ω) / n)
             = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω
  2. rw [e], pull out the constant, split the variance of the sum:           R9, R10 (its pairwise argument by R11)
       goal: (↑n)⁻¹ ^ 2 * ∑ i ∈ Finset.range n, Var[X i; μ] ≤ C / ↑n
  3. hs : ∑ i ∈ Finset.range n, Var[X i; μ] ≤ n * C
       a `calc`: termwise bound by hvar, then the sum of constants:          R12, R4
  4. hn' : (0 : ℝ) < n                                                       R13
  5. A `calc`: multiply hs by (↑n)⁻¹ ^ 2, then simplify to C / ↑n:           R14, R5
-/
-- MILESTONE (optional: change or delete)
theorem sample_mean_variance_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (C : ℝ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hvar : ∀ i, Var[X i; μ] ≤ C)
    (n : ℕ) (hn : 0 < n) :
    Var[fun ω => (∑ i ∈ Finset.range n, X i ω) / n; μ] ≤ C / n := by
  have e : (fun ω => (∑ i ∈ Finset.range n, X i ω) / n) =
      fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω := by
    funext ω; simp [Finset.sum_apply]; ring
  rw [e, variance_const_mul, IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]
  have hs : ∑ i ∈ Finset.range n, Var[X i; μ] ≤ n * C := by
    calc _ ≤ ∑ i ∈ Finset.range n, C := Finset.sum_le_sum fun i _ => hvar i
      _ = n * C := by simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ)⁻¹ ^ 2 * ∑ i ∈ Finset.range n, Var[X i; μ] ≤ (n : ℝ)⁻¹ ^ 2 * (n * C) := by gcongr
    _ = C / n := by field_simp

/- SKELETON · tail_bound   (milestone 3: Chebyshev; uses milestones 1 and 2)
  1. hY : MemLp (fun ω => (∑ i ∈ Finset.range n, X i ω) / n) 2 μ
       L² of the sum, times (↑n)⁻¹; then match the two functions:           R15, R16, R17, then R6 → R7 → R8
  2. Chebyshev for the sample mean at ε:                                     R18
  3. Milestone 1 turns the mean inside `h` into `m`:                         R19
  4. `dist` → `|· - ·|` in the goal, so it matches `h`:                       R20
  5. Go through `h`; compare the two `ENNReal.ofReal`s:                      R21, R22
       goal: Var[…] / ε ^ 2 ≤ C / (↑n * ε ^ 2)
  6. With milestone 2 in the context, a `calc`:
       Var[…] / ε ^ 2 ≤ C / ↑n / ε ^ 2 = C / (↑n * ε ^ 2)                   R14, R23
-/
-- MILESTONE (optional: change or delete)
theorem tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m C : ℝ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m) (hvar : ∀ i, Var[X i; μ] ≤ C) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (hn : 0 < n) :
    μ {ω | ε ≤ dist ((∑ i ∈ Finset.range n, X i ω) / n) m} ≤ ENNReal.ofReal (C / (n * ε ^ 2)) := by
  have hY : MemLp (fun ω => (∑ i ∈ Finset.range n, X i ω) / n) 2 μ := by
    have := (memLp_finsetSum' (Finset.range n) (fun i _ => hL2 i)).const_mul (n : ℝ)⁻¹
    convert this using 1
    funext ω; simp [Finset.sum_apply]; ring
  have h := meas_ge_le_variance_div_sq hY hε
  rw [sample_mean_mean μ X m hL2 hmean n hn] at h
  simp only [Real.dist_eq]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hv := sample_mean_variance_le μ X C hL2 hindep hvar n hn
  calc Var[fun ω => (∑ i ∈ Finset.range n, X i ω) / n; μ] / ε ^ 2 ≤ C / n / ε ^ 2 := by gcongr
    _ = C / (n * ε ^ 2) := by rw [div_div]

/- SKELETON · weak_law
  Prove the milestones first: sample_mean_mean (used in tail_bound, step 3),
  sample_mean_variance_le (tail_bound, step 6), tail_bound (step 4 below).
  1. Unfold convergence in measure; intro ε hε:                              R24
  2. hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C / (n * ε ^ 2))) atTop (𝓝 0)
       move the limit into ℝ:                                                R25, R26
       `C / ε ^ 2 / ↑n → 0`, then match the terms:                           R27, R28, then R23, rw [mul_comm]
  3. Squeeze between the constant 0 and the bound of hlim;
     the lower bound holds everywhere:                                       R29, R30, R31, R32
  4. The upper bound for n ≥ 1, by tail_bound (`1 ≤ n` is `0 < n`):         R33, R34
-/
-- BEGIN SPEC
theorem weak_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m C : ℝ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m) (hvar : ∀ i, Var[X i; μ] ≤ C) :
    TendstoInMeasure μ (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, X i ω) / n) atTop (fun _ => m) :=
-- END SPEC
  by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C / (n * ε ^ 2))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      apply ENNReal.tendsto_ofReal
      have := (tendsto_const_div_atTop_nhds_zero_nat (C / ε ^ 2))
      refine this.congr fun n => ?_
      rw [div_div, mul_comm]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact tail_bound μ X m C hL2 hindep hmean hvar ε hε n hn

end H050

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three milestones, then a squeeze: `E X̄ₙ = m` (linearity); `Var X̄ₙ = n⁻² ∑ Var (X i) ≤ C / n`
    (independence kills the covariances); Chebyshev gives `P(|X̄ₙ - m| ≥ ε) ≤ C / (n ε²)`, which tends to `0`.
    Probabilities are in `ℝ≥0∞`, so the bound is `ENNReal.ofReal (C / (n * ε ^ 2))`.
H2. Mean: `integral_div`, `integral_finsetSum` (integrable from `MemLp.integrable one_le_two`), `simp [hmean]`,
    `field_simp`. Variance: first prove the restatement of the sample mean as
    `fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω` (`funext`, `simp [Finset.sum_apply]`, `ring`), then
    `variance_const_mul` and `IndepFun.variance_sum`; bound by `Finset.sum_le_sum`, finish with `gcongr` /
    `field_simp`. Tail: `MemLp` via `memLp_finsetSum'`, `.const_mul`, `convert … using 1`; then
    `meas_ge_le_variance_div_sq`, milestone 1 `at h`, `Real.dist_eq`, `ENNReal.ofReal_le_ofReal`.
    Main: `rw [tendstoInMeasure_iff_dist]` and squeeze between `0` and the bound.
H3. Variance: `rw [e, variance_const_mul, IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]`.
    Limit of the bound: `rw [← ENNReal.ofReal_zero]; apply ENNReal.tendsto_ofReal`, then
    `(tendsto_const_div_atTop_nhds_zero_nat (C / ε ^ 2)).congr fun n => ?_` and `rw [div_div, mul_comm]`.
    Squeeze: `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim (Eventually.of_forall fun _ => bot_le) ?_`,
    then `filter_upwards [eventually_ge_atTop 1] with n hn`.
-/

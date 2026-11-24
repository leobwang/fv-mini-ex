/- H050 | Weak law of large numbers | 1-1.5 h | TendstoInMeasure, Chebyshev, variance of sums, ENNReal limits, squeeze, mathlib
GOAL
  Pairwise independent `L²` variables `X i` with common mean `m` and `Var (X i) ≤ C`: the sample mean
  `X̄ₙ = (X 0 + … + X (n-1)) / n` converges to `m` in probability (`P(|X̄ₙ - m| ≥ ε) → 0` for every `ε > 0`).
  Bound `Var X̄ₙ ≤ C / n`, apply Chebyshev, then squeeze the probabilities (values in `ℝ≥0∞`) to `0`.

REFERENCE
  `μ[X]`: E X;  `Var[X; μ]`: variance;  `X ⟂ᵢ[μ] Y`: X, Y independent;  `MemLp X 2 μ`: E X² < ∞;  `μ s : ℝ≥0∞`;  `𝓝 a`: neighbourhood filter (`Tendsto f atTop (𝓝 a)` means `f n → a`).
  #check tendstoInMeasure_iff_dist  -- TendstoInMeasure μ f l g ↔ ∀ ε, 0 < ε → Tendsto (fun i => μ {x | ε ≤ dist (f i x) (g x)}) l (𝓝 0)
  #check meas_ge_le_variance_div_sq -- MemLp X 2 μ → 0 < c → μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2)
  #check IndepFun.variance_sum      -- (∀ i ∈ s, MemLp (X i) 2 μ) → (↑s).Pairwise (fun i j => X i ⟂ᵢ[μ] X j) → Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, Var[X i; μ]
  #check variance_const_mul         -- (c X μ) : Var[fun ω => c * X ω; μ] = c ^ 2 * Var[X; μ]
  #check memLp_finsetSum'           -- (s) : (∀ i ∈ s, MemLp (f i) p μ) → MemLp (∑ i ∈ s, f i) p μ;   then `.const_mul c`
  #check integral_finsetSum         -- (s) : (∀ i ∈ s, Integrable (f i) μ) → ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ  (and `integral_div`)
  #check ENNReal.tendsto_ofReal     -- Tendsto m f (𝓝 a) → Tendsto (fun x => ENNReal.ofReal (m x)) f (𝓝 (ENNReal.ofReal a))
  #check tendsto_const_div_atTop_nhds_zero_nat  -- (C) : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0)
  #check tendsto_of_tendsto_of_tendsto_of_le_of_le'  -- squeeze: g → a → h → a → (∀ᶠ b, g b ≤ f b) → (∀ᶠ b, f b ≤ h b) → f → a
  -- `Finset.sum_apply`: `(∑ i ∈ s, X i) ω = ∑ i ∈ s, X i ω`;  `bot_le : ⊥ ≤ x` is `0 ≤ x` in `ℝ≥0∞`
NOTE: `X̄ₙ` is written `fun ω => (∑ i ∈ Finset.range n, X i ω) / n`; rewrite it as `(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω` before using the variance lemmas.
-/
import Mathlib

namespace H050

open MeasureTheory ProbabilityTheory Filter Topology

-- MILESTONE (optional: change or delete)
theorem sample_mean_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m : ℝ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (n : ℕ) (hn : 0 < n) :
    μ[fun ω => (∑ i ∈ Finset.range n, X i ω) / n] = m := by
  rw [integral_div, integral_finsetSum _ (fun i _ => (hL2 i).integrable one_le_two)]
  simp [hmean]
  field_simp

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
H1. Three steps: `E X̄ₙ = m`; `Var X̄ₙ = (1/n²) ∑ Var (X i) ≤ C / n`; Chebyshev gives `P(|X̄ₙ - m| ≥ ε) ≤ C / (n ε²)`, and the right side tends to `0`.
H2. Variance: `funext` the sample mean into `(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω`, then `variance_const_mul` and `IndepFun.variance_sum` (the pairwise argument is `fun i _ j _ hij => hindep hij`); bound the sum by `Finset.sum_le_sum` and finish with `gcongr` / `field_simp`. Main: `rw [tendstoInMeasure_iff_dist]`, squeeze between `0` and `ENNReal.ofReal (C / (n * ε ^ 2))`.
H3. Limit of the bound: `rw [← ENNReal.ofReal_zero]; apply ENNReal.tendsto_ofReal; exact (tendsto_const_div_atTop_nhds_zero_nat (C / ε ^ 2)).congr fun n => by rw [div_div, mul_comm]`. Squeeze: `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim (Eventually.of_forall fun _ => bot_le) ?_`, then `filter_upwards [eventually_ge_atTop 1] with n hn`.
-/

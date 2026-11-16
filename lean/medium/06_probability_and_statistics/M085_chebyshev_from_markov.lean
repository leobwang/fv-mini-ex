/- M085 | Chebyshev from Markov | 10-15 min | variance, Markov, set rewriting, MemLp, mathlib
GOAL
  Chebyshev's inequality `P(|X - E X| ≥ c) ≤ Var X / c²` for `c > 0`, by applying Markov's
  inequality (allowed here) to the nonnegative variable `(X - E X)²`.

REFERENCE
  `μ.real s : ℝ` is the probability of `s`; `μ[X]` is `∫ ω, X ω ∂μ`; `MemLp X 2 μ`: `E[X²] < ∞`.
  `Var[X; μ]` is the variance of `X` under `μ` (`ProbabilityTheory.variance X μ`).
  #check mul_meas_ge_le_integral_of_nonneg  -- 0 ≤ᵐ[μ] f → Integrable f μ → ∀ ε, ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ
  #check variance_eq_integral  -- AEMeasurable X μ → Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
  example (hX : MemLp X 2 μ) (c : ℝ) : Integrable (fun ω => (X ω - c) ^ 2) μ :=
    (hX.sub (memLp_const c)).integrable_sq   -- and `hX.aemeasurable : AEMeasurable X μ`
  #check Filter.Eventually.of_forall  -- (∀ x, p x) → ∀ᶠ x in f, p x   (builds `0 ≤ᵐ[μ] f`)
  #check sq_abs                -- |a| ^ 2 = a ^ 2
  #check pow_le_pow_iff_left₀  -- 0 ≤ a → 0 ≤ b → n ≠ 0 → (a ^ n ≤ b ^ n ↔ a ≤ b)
  #check le_div_iff₀           -- 0 < c → (a ≤ b / c ↔ a * c ≤ b)
BANNED: meas_ge_le_variance_div_sq, meas_ge_le_evariance_div_sq, pow_mul_meas_ge_le_eLpNorm, mul_meas_ge_le_pow_eLpNorm, mul_meas_ge_le_pow_eLpNorm', meas_ge_le_mul_pow_eLpNorm_enorm
-/
import Mathlib

namespace M085

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem chebyshev {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω - μ[X]|} ≤ Var[X; μ] / c ^ 2 :=
-- END SPEC
  sorry

end M085

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The event `c ≤ |X - E X|` is the same event as `c² ≤ (X - E X)²`, and the expectation of
    `(X - E X)²` is exactly `Var X`.
H2. Prove the set equality with `ext ω`, then call Markov on `fun ω => (X ω - μ[X]) ^ 2` at level
    `c ^ 2`, rewrite its right side into `Var[X; μ]` and its set back into the original one.
H3. `have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - μ[X])) hint (c ^ 2)`,
    then `rw [← variance_eq_integral hX.aemeasurable, ← hset] at hm`, `rw [le_div_iff₀ (by positivity)]`, `linarith`.
-/

/- M089 | Mean squared error decomposition | 15 min | bias-variance, integral algebra, Integrable, mathlib
GOAL
  Bias-variance for a constant guess `c`: `E[(X - c)²] = Var X + (E X - c)²`. Then deduce that
  `c = E X` has the least mean squared error among all constants.

REFERENCE
  `μ[X]` is `∫ ω, X ω ∂μ`; `MemLp X 2 μ`: `E[X²] < ∞`; `Var[X; μ]` is the variance.
  #check variance_eq_sub    -- MemLp X 2 μ → Var[X; μ] = ∫ x, (X ^ 2) x ∂μ - (∫ x, X x ∂μ) ^ 2
  #check integral_add       -- Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ f + ∫ g
  #check integral_sub       -- same shape for `-`
  #check integral_const_mul -- ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
  #check integral_const     -- ∫ x, c ∂μ = μ.real Set.univ • c     (`probReal_univ : μ.real univ = 1`)
  example (hX : MemLp X 2 μ) : Integrable X μ := hX.integrable one_le_two   -- also `hX.integrable_sq`
  example (hX : Integrable X μ) : Integrable (fun ω => 2 * c * X ω) μ := hX.const_mul _
  `Pi.pow_apply : (f ^ n) x = f x ^ n` unfolds the `X ^ 2` that `variance_eq_sub` produces.
NOTE: `rw [integral_add hf hg]` matches only when `hf`, `hg` are stated as `Integrable (fun ω => ...) μ`.
-/
import Mathlib

namespace M089

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem mse_decomposition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    μ[fun ω => (X ω - c) ^ 2] = Var[X; μ] + (μ[X] - c) ^ 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mean_minimizes_mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    μ[fun ω => (X ω - μ[X]) ^ 2] ≤ μ[fun ω => (X ω - c) ^ 2] :=
-- END SPEC
  sorry

end M089

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Expand `(X - c)² = X² - 2cX + c²`, integrate term by term, and compare with `E[X²] - (E X)²`.
H2. Rewrite the integrand with a `funext` equation, then `integral_add` / `integral_sub` /
    `integral_const_mul` / `integral_const`. The second theorem is the first one used twice.
H3. `have h1 : Integrable (fun ω => X ω ^ 2 - 2 * c * X ω) μ := hX2.sub (hXi.const_mul _)`; then
    `rw [variance_eq_sub hX, e, integral_add h1 (integrable_const _), integral_sub hX2 h2, integral_const_mul]`,
    `simp only [Pi.pow_apply, integral_const, probReal_univ, smul_eq_mul, one_mul]; ring`.
    Second: rewrite both sides with `mse_decomposition`; the difference is `(μ[X] - c) ^ 2 ≥ 0`.
-/

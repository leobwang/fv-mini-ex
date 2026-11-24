/- E096 | Expectation is linear | 2-3 min | integral, μ[X] notation, Integrable, integral_add, integral_const, mathlib
GOAL
  Linearity of expectation: `E[a X + b] = a E[X] + b` for an integrable random variable `X : Ω → ℝ`.

REFERENCE
  `μ[X]` is notation (from `open ProbabilityTheory`) for `∫ ω, X ω ∂μ`, the expectation of `X` under `μ`.
  `Integrable X μ`: `X` is (a.e. strongly) measurable and `∫ |X| ∂μ < ∞`. Additivity needs it.
  #check integral_add          -- Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ f + ∫ g
  #check integral_const_mul    -- ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ   (no integrability needed)
  #check integral_const        -- ∫ x, c ∂μ = μ.real Set.univ • c
  #check Integrable.const_mul  -- Integrable f μ → ∀ c, Integrable (fun x => c * f x) μ
  #check integrable_const      -- (c : β) → Integrable (fun _ => c) μ   (μ a finite measure)
  `simp` knows `μ.real Set.univ = 1` for a probability measure and `c • x = c * x` on `ℝ`.
-/
import Mathlib

namespace E096

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem expectation_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (a b : ℝ) :
    μ[fun ω => a * X ω + b] = a * μ[X] + b :=
-- END SPEC
  sorry

end E096

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split the integral of the sum first; both summands must be shown integrable.
H2. `rw [integral_add h1 h2]` with `h1 : Integrable (fun ω => a * X ω) μ` and the constant one, then
    pull `a` out and evaluate the integral of the constant `b`.
H3. `rw [integral_add (hX.const_mul a) (integrable_const b), integral_const_mul]; simp`.
-/

/- E099 | Independent random variables | 2 min | IndepFun, ⟂ᵢ notation, integral_mul_eq_mul_integral, mathlib
GOAL
  For independent random variables `X` and `Y`, `E[X Y] = E[X] E[Y]`; with `E[X] = 2` and `E[Y] = 3`
  conclude `E[X Y] = 6`.

REFERENCE
  `X ⟂ᵢ[μ] Y` is notation for `IndepFun X Y μ`: `X` and `Y` are independent under `μ`.
  `X * Y` is the pointwise product `fun ω => X ω * Y ω`, so `μ[X * Y]` is `E[X Y]`.
  #check IndepFun.integral_mul_eq_mul_integral
    -- X ⟂ᵢ[μ] Y → AEStronglyMeasurable X μ → AEStronglyMeasurable Y μ → ∫ x, (X * Y) x ∂μ = μ[X] * μ[Y]
  #check Measurable.aestronglyMeasurable    -- Measurable f → AEStronglyMeasurable f μ
  Dot notation: `hXY.integral_mul_eq_mul_integral h1 h2` for `hXY : X ⟂ᵢ[μ] Y`.
-/
import Mathlib

namespace E099

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem indep_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : X ⟂ᵢ[μ] Y)
    (h1 : μ[X] = 2) (h2 : μ[Y] = 3) : μ[X * Y] = 6 :=
-- END SPEC
  by
    rw [hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable, h1, h2]
    norm_num

end E099

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Factor the expectation of the product, then substitute the two given means.
H2. The factoring lemma wants `AEStronglyMeasurable`; you have `Measurable`, which converts by dot notation.
H3. `rw [hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable, h1, h2]; norm_num`.
-/

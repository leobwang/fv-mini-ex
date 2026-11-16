/- E097 | Variance of an affine map | 2 min | variance, Var notation, AEStronglyMeasurable, mathlib
GOAL
  `Var(a X + b) = a² Var(X)`: shifting does not change the variance, scaling by `a` multiplies it by `a²`.

REFERENCE
  `Var[X; μ]` is the variance, `∫ ω, (X ω - μ[X]) ^ 2 ∂μ` for measurable `X` (real-valued; it is 0 when
  `X` is not square-integrable). `fun ω => a * X ω + b` is the random variable `a X + b`.
  `AEStronglyMeasurable X μ`: `X` agrees `μ`-a.e. with a measurable function (the weakest measurability).
  #check variance_add_const              -- AEStronglyMeasurable X μ → ∀ c, Var[fun ω => X ω + c; μ] = Var[X; μ]
  #check variance_const_mul              -- (c X μ) → Var[fun ω => c * X ω; μ] = c ^ 2 * Var[X; μ]
  #check AEStronglyMeasurable.const_mul  -- AEStronglyMeasurable f μ → ∀ c, AEStronglyMeasurable (fun x => c * f x) μ
-/
import Mathlib

namespace E097

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem variance_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ) (a b : ℝ) :
    Var[fun ω => a * X ω + b; μ] = a ^ 2 * Var[X; μ] :=
-- END SPEC
  sorry

end E097

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read `a * X ω + b` as `Y ω + b` with `Y = fun ω => a * X ω`.
H2. Remove the `+ b` first (that lemma needs measurability of `Y`), then pull out the `a`.
H3. `rw [variance_add_const (hX.const_mul a), variance_const_mul]`.
-/

/- E101 | Laws: the Gaussian | 2 min | HasLaw, gaussianReal, distribution of a random variable, mathlib
GOAL
  If `X` has the normal law `N(m, v)` under `P`, then `E[X] = m` and `Var(X) = v`.

REFERENCE
  `HasLaw X μ P`: the distribution of `X : Ω → 𝓧` under `P` is `μ` (`P.map X = μ`, `X` a.e.-measurable).
  `gaussianReal m v : Measure ℝ` is `N(m, v)`, mean `m : ℝ`, variance `v : ℝ≥0` (nonnegative reals).
  `(v : ℝ)` is the coercion `ℝ≥0 → ℝ`, inserted automatically in `Var[X; P] = v`.
  #check HasLaw.integral_eq          -- HasLaw X μ P → ∫ x, X x ∂P = ∫ x, x ∂μ
  #check HasLaw.variance_eq          -- HasLaw X μ P → Var[X; P] = Var[id; μ]     (X real-valued)
  #check integral_id_gaussianReal    -- ∫ x, x ∂gaussianReal m v = m
  #check variance_id_gaussianReal    -- Var[id; gaussianReal m v] = ↑v
  The lesson: move a question about `X` to a question about its law, then ask the law.
-/
import Mathlib

namespace E101

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem gaussian_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (m : ℝ)
    (v : ℝ≥0) (hX : HasLaw X (gaussianReal m v) P) : P[X] = m ∧ Var[X; P] = v :=
-- END SPEC
  sorry

end E101

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Neither conjunct mentions `Ω` once you replace `X` by its law.
H2. Prove each conjunct with two rewrites: first the `HasLaw` lemma, then the Gaussian fact.
H3. `⟨by rw [hX.integral_eq, integral_id_gaussianReal], by rw [hX.variance_eq, variance_id_gaussianReal]⟩`.
-/

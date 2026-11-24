/- M088 | Variance of a 0/1 variable | 10 min | variance_eq_sub, bounded functions are L², X² = X, mathlib
GOAL
  A Bernoulli-type variable (`X ω ∈ {0, 1}` for every `ω`) has `Var X = p (1 - p)` where `p = E X`.

REFERENCE
  `μ[X]` is `∫ ω, X ω ∂μ`. `Var[X; μ]` is the variance of `X` under `μ` (`ProbabilityTheory.variance X μ`).
  `MemLp X 2 μ`: `X` is square-integrable (`E[X²] < ∞`).
  #check variance_eq_sub    -- MemLp X 2 μ → Var[X; μ] = ∫ x, (X ^ 2) x ∂μ - (∫ x, X x ∂μ) ^ 2
  #check memLp_of_bounded   -- (∀ᵐ x ∂μ, f x ∈ Set.Icc a b) → AEStronglyMeasurable f μ → ∀ p, MemLp f p μ
  #check Filter.Eventually.of_forall  -- (∀ x, p x) → ∀ᶠ x in f, p x   (an everywhere fact is a.e.)
  example (X : Ω → ℝ) (hX : Measurable X) : AEStronglyMeasurable X μ := hX.aestronglyMeasurable
  `X ^ 2` is the pointwise square of the function `X` (`(X ^ 2) ω = X ω ^ 2`); prove equalities of
  functions with `funext ω`.
BANNED: variance_of_ae_eq_zero_or_one, condVar_of_ae_eq_zero_or_one, integral_one_sub_of_ae_eq_zero_or_one
-/
import Mathlib

namespace M088

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem bernoulli_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) :
    Var[X; μ] = μ[X] * (1 - μ[X]) :=
-- END SPEC
  by
    have hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1 := Filter.Eventually.of_forall fun ω => by
      rcases h01 ω with h | h <;> simp [h]
    have hL2 : MemLp X 2 μ := memLp_of_bounded hb hX.aestronglyMeasurable 2
    have hsq : X ^ 2 = X := by
      funext ω
      rcases h01 ω with h | h <;> simp [h]
    rw [variance_eq_sub hL2, hsq]
    ring

end M088

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Use `Var X = E[X²] - (E X)²`. For a 0/1 variable, `X² = X`.
H2. That formula needs `MemLp X 2 μ`: `X` takes values in `[0, 1]`, so it is bounded. Then show the
    function equality `X ^ 2 = X` and rewrite.
H3. `have hL2 : MemLp X 2 μ := memLp_of_bounded (a := 0) (b := 1) (Filter.Eventually.of_forall ...) hX.aestronglyMeasurable 2`;
    `have hsq : X ^ 2 = X := by funext ω; rcases h01 ω with h | h <;> simp [h]`; `rw [variance_eq_sub hL2, hsq]; ring`.
-/

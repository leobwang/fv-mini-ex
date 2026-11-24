/- M088 | Variance of a 0/1 variable | 10 min | variance_eq_sub, bounded functions are L², X² = X, mathlib
GOAL
  A Bernoulli-type variable (`X ω ∈ {0, 1}` for every `ω`) has `Var X = p (1 - p)` where `p = E X`.
BANNED: variance_of_ae_eq_zero_or_one, condVar_of_ae_eq_zero_or_one, integral_one_sub_of_ae_eq_zero_or_one

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M088

/- SKELETON · bernoulli_variance
  1. The bound, almost everywhere (state the type with `(0 : ℝ)`):
       hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1
     proof: R1, intro ω, then R2 on `h01 ω` and in both goals R4 (R3 inside)
  2. Square-integrability from the bound:
       hL2 : MemLp X 2 μ                                                   R6 with hb and R5
  3. The function equation
       hsq : X ^ 2 = X
     proof: R7, then R2 on `h01 ω` and `simp [h]` in both goals (R8 inside)
  4. Open the variance, then replace `X ^ 2` under the integral:          R9 (with hL2), R10 (rw [hsq])
  5. What is left is `p - p ^ 2 = p * (1 - p)` with `p = ∫ X`:             R11
-/
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
H1. Use `Var X = E[X²] - (E X)²` (`variance_eq_sub`). For a 0/1 variable `X² = X` as functions, so
    `E[X²] = E X`. The formula needs `MemLp X 2 μ`: get it from `0 ≤ X ≤ 1`.
H2. Three `have`s, then two rewrites: `hb` (the bound a.e., R1–R4), `hL2 : MemLp X 2 μ` (R5, R6),
    `hsq : X ^ 2 = X` (`funext ω`, then split `h01 ω`); `rw [variance_eq_sub hL2, hsq]`; `ring`.
H3. `have hL2 : MemLp X 2 μ := memLp_of_bounded hb hX.aestronglyMeasurable 2` with
    `hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1`, proved by `apply Filter.Eventually.of_forall; intro ω;
    rcases h01 ω with h | h <;> simp [h]`. `hsq`: `funext ω; rcases h01 ω with h | h <;> simp [h]`.
-/

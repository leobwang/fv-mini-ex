/- M089 | Mean squared error decomposition | 15 min | bias-variance, integral algebra, Integrable, mathlib
GOAL
  Bias-variance for a constant guess `c`: `E[(X - c)²] = Var X + (E X - c)²`. Then deduce that
  `c = E X` has the least mean squared error among all constants.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M089

/- SKELETON · mse_decomposition
  1. Integrability facts, each a `have` with its type written out in `fun ω => …` form:
       hXi : Integrable X μ                                                R1
       hX2 : Integrable (fun ω => X ω ^ 2) μ                               R2
       h2  : Integrable (fun ω => 2 * c * X ω) μ                           R3
       h1  : Integrable (fun ω => X ω ^ 2 - 2 * c * X ω) μ                 R4 (with R3 inside)
  2. The integrand identity
       e : (fun ω => (X ω - c) ^ 2) = fun ω => X ω ^ 2 - 2 * c * X ω + c ^ 2
     proof:                                                                R6 → R7
  3. Open the variance, then replace the integrand:                        R8, R9 (rw [e])
  4. Split the integral from the outside in:
       `… + c ^ 2` with h1 and the constant                                R10 with R5
       `X² - 2cX` with hX2 and h2                                          R11
       pull `2 * c` out                                                    R12
  5. Clean up `(X ^ 2) x`, `∫ c ^ 2`, `μ.real univ`, `1 • _` in one `simp only`:   R13–R16
  6. What is left is a polynomial identity in `∫ X`, `∫ X ^ 2`, `c`:        R7
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem mse_decomposition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    μ[fun ω => (X ω - c) ^ 2] = Var[X; μ] + (μ[X] - c) ^ 2 :=
-- END SPEC
  sorry

/- SKELETON · mean_minimizes_mse
  1. Rewrite both sides with `mse_decomposition μ X hX` (leave `c` open);
     each rewrite fixes `c` at its first match, so rewrite twice:          R17, R17
  2. The goal is now `Var + (E X - E X)² ≤ Var + (E X - c)²`; close it with
     the hint `0 ≤ (μ[X] - c) ^ 2`:                                         R18 inside R19
-/
-- BEGIN SPEC
theorem mean_minimizes_mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    μ[fun ω => (X ω - μ[X]) ^ 2] ≤ μ[fun ω => (X ω - c) ^ 2] :=
-- END SPEC
  sorry

end M089

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Expand `(X - c)² = X² - 2cX + c²`, integrate term by term, and compare with `E[X²] - (E X)²`.
    The second theorem is the first one used twice, plus `(E X - c)² ≥ 0`.
H2. First the integrability `have`s (R1–R4), stated as `Integrable (fun ω => …) μ`, and the integrand
    equation `e` (`funext ω; ring`). Then `rw [variance_eq_sub hX, e]`, split with `integral_add` /
    `integral_sub` / `integral_const_mul`, `simp only` the rest (R13–R16), and finish with `ring`.
H3. `have h1 : Integrable (fun ω => X ω ^ 2 - 2 * c * X ω) μ := hX2.sub (hXi.const_mul _)`; then
    `rw [variance_eq_sub hX, e, integral_add h1 (integrable_const _), integral_sub hX2 h2, integral_const_mul]`,
    `simp only [Pi.pow_apply, integral_const, probReal_univ, smul_eq_mul, one_mul]; ring`.
    Second: `rw [mse_decomposition μ X hX]` twice; then `nlinarith` with the hint `sq_nonneg (μ[X] - c)`.
-/

/- E098 | A fair die | 2-3 min | PMF, uniformOfFintype, toMeasure, integral_eq_sum, Fin, mathlib
GOAL
  Model a fair six-sided die as the uniform distribution on `Fin 6` (faces `0..5`, read as `1..6`).
  Show each face has probability `1/6` and the expected face value `E[i + 1]` is `7/2`.

REFERENCE
  `PMF α`: a probability mass function, `p : α → ℝ≥0∞` with `∑' a, p a = 1`; `p.toMeasure` is its measure.
  `PMF.uniformOfFintype α` gives every element of a finite type the mass `1 / card α`.
  #check PMF.uniformOfFintype_apply    -- uniformOfFintype α a = (↑(Fintype.card α))⁻¹
  #check PMF.toMeasure_apply_singleton -- (p a) → MeasurableSet {a} → p.toMeasure {a} = p a
  #check measurableSet_singleton       -- (x : α) → MeasurableSet {x}   (on `Fin n`, `ℕ`, `ℝ`, …)
  #check PMF.integral_eq_sum           -- ∫ a, f a ∂p.toMeasure = ∑ a, (p a).toReal • f a   (finite α)
  #check Fin.sum_univ_succ             -- ∑ i : Fin (n+1), f i = f 0 + ∑ i : Fin n, f i.succ
  `(i : ℕ)` is the value of `i : Fin 6` as a natural number; `simp` knows `Fintype.card (Fin 6) = 6`.
NOTE: plain `simp` closes `die_face`; do the rewrite chain first to learn the `toMeasure` API.
-/
import Mathlib

namespace E098

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem die_face : ∀ i : Fin 6, (PMF.uniformOfFintype (Fin 6)).toMeasure {i} = 6⁻¹ :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem die_mean :
    ∫ i, ((i : ℕ) + 1 : ℝ) ∂(PMF.uniformOfFintype (Fin 6)).toMeasure = 7 / 2 :=
-- END SPEC
  sorry

end E098

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Turn the measure of a singleton, and the integral over a finite type, into statements about the PMF.
H2. `die_face`: `intro i`, rewrite with the singleton lemma, then with the uniform mass; `simp` finishes.
    `die_mean`: `rw [PMF.integral_eq_sum]`, then unfold the sum over `Fin 6` into six terms.
H3. `intro i; rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), PMF.uniformOfFintype_apply]; simp`;
    `rw [PMF.integral_eq_sum]; simp [Fin.sum_univ_succ]; norm_num`.
-/

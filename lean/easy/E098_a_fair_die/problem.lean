/- E098 | A fair die | 2-3 min | PMF, uniformOfFintype, toMeasure, integral_eq_sum, Fin, mathlib
GOAL
  Model a fair six-sided die as the uniform distribution on `Fin 6` (faces `0..5`, read as `1..6`).
  Show each face has probability `1/6` and the expected face value `E[i + 1]` is `7/2`.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E098

/- SKELETON · die_face
  1. Introduce the face:                                                    intro i
  2. Measure of the point {i} → the PMF's weight at i; pass the
     measurability proof as the third argument so no side goal is left:     R1 with R2
  3. Uniform weight → (↑(Fintype.card (Fin 6)))⁻¹:                           R3
  4. Evaluate the count and the cast ℕ → ENNReal:                           simp (it applies R4, R5)
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem die_face : ∀ i : Fin 6, (PMF.uniformOfFintype (Fin 6)).toMeasure {i} = 6⁻¹ :=
-- END SPEC
  sorry

/- SKELETON · die_mean
  1. Integral over the finite type Fin 6 → weighted sum ∑ a, (p a).toReal • f a:   R6
  2. One `simp` with the unrolling lemma named; in each of the six terms it does
       weight → 6⁻¹ as a real number                                       R3, R4, R5 → R7 → R8
       `•` → `*`                                                           R9
       sum over Fin 6 → six terms                                          R10 (repeated)
       index values ↑0, ↑j.succ and the cast ℕ → ℝ                         R12, R11, R13
  3. Add up the remaining numerals:                                        norm_num
-/
-- BEGIN SPEC
theorem die_mean :
    ∫ i, ((i : ℕ) + 1 : ℝ) ∂(PMF.uniformOfFintype (Fin 6)).toMeasure = 7 / 2 :=
-- END SPEC
  sorry

end E098

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both statements are about the measure `toMeasure` of a PMF. Turn the measure of a point into the PMF's
    weight (R1), and the integral over the finite type `Fin 6` into a finite sum (R6); then it is arithmetic.
H2. `die_face`: `intro i`, rewrite with R1 (measurability from R2) and with R3; `simp` finishes.
    `die_mean`: rewrite with R6, then let `simp` unroll the sum over `Fin 6` (R10) and evaluate the six terms;
    `norm_num` adds them up.
H3. `rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), PMF.uniformOfFintype_apply]`;
    `rw [PMF.integral_eq_sum]` then `simp [Fin.sum_univ_succ]`.
-/

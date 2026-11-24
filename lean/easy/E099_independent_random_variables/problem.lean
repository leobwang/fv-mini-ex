/- E099 | Independent random variables | 2 min | IndepFun, ⟂ᵢ notation, integral_mul_eq_mul_integral, mathlib
GOAL
  For independent random variables `X` and `Y`, `E[X Y] = E[X] E[Y]`; with `E[X] = 2` and `E[Y] = 3`
  conclude `E[X Y] = 6`.

GUIDE
  Entries R1–R4: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E099

/- SKELETON · indep_mul
  1. Turn `hX`, `hY` into the side conditions the product rule wants:      R1
       hX.aestronglyMeasurable : AEStronglyMeasurable X μ   (same for Y)
     Write these inline as arguments in step 2 (`μ` is then read off the goal). A separate
     `have` needs the type written out, `have hX' : AEStronglyMeasurable X μ := …`.
  2. Factor the mean of the product, `μ[X * Y]` → `μ[X] * μ[Y]`,
     passing the two proofs from step 1:                                   R2
  3. Substitute the given means, first `h1`, then `h2`:                    R3, R3
       goal: 2 * 3 = 6
  4. Finish the numbers:                                                   R4
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem indep_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : X ⟂ᵢ[μ] Y)
    (h1 : μ[X] = 2) (h2 : μ[Y] = 3) : μ[X * Y] = 6 :=
-- END SPEC
  sorry

end E099

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Factor the expectation of the product (R2), then substitute the two given means (R3).
H2. The factoring lemma is `hXY.integral_mul_eq_mul_integral`; its two measurability arguments must be
    `AEStronglyMeasurable`. You have `Measurable`, which converts by dot notation (R1). One `rw` chain,
    then `norm_num` (R4).
H3. `rw [hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable, h1, h2]; norm_num`.
-/

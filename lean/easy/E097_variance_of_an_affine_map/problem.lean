/- E097 | Variance of an affine map | 2 min | variance, Var notation, AEStronglyMeasurable, mathlib
GOAL
  `Var(a X + b) = a² Var(X)`: shifting does not change the variance, scaling by `a` multiplies it by `a²`.

GUIDE
  Entries R1–R3: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E097

/- SKELETON · variance_affine
  Read the left side as `Var[Y + b]` with `Y = fun ω => a * X ω`; the outermost operation is `+ b`.
  1. Measurability of `Y`, from `hX` (a term, or a `have`):               R1
       AEStronglyMeasurable (fun x => a * X x) μ
  2. Remove the shift `+ b`, giving `rw` the fact from step 1:            R2
       goal: Var[fun x => a * X x; μ] = a ^ 2 * Var[X; μ]
  3. Pull the factor `a` out as `a ^ 2`; `rw` then closes the goal:       R3
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem variance_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ) (a b : ℝ) :
    Var[fun ω => a * X ω + b; μ] = a ^ 2 * Var[X; μ] :=
-- END SPEC
  sorry

end E097

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read `a * X ω + b` as `Y ω + b` with `Y = fun ω => a * X ω`: first the shift, then the scaling.
H2. Rewrite with `variance_add_const` (R2), which needs `AEStronglyMeasurable Y μ` for this `Y`, not for `X`:
    build it from `hX` with R1. Then `variance_const_mul` (R3) needs no argument.
H3. `rw [variance_add_const (hX.const_mul a), …]`: the second rewrite in the list is R3, and it closes the goal.
-/

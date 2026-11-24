/- E096 | Expectation is linear | 2-3 min | integral, μ[X] notation, Integrable, integral_add, integral_const, mathlib
GOAL
  Linearity of expectation: `E[a X + b] = a E[X] + b` for an integrable random variable `X : Ω → ℝ`.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E096

/- SKELETON · expectation_affine
  The infoview shows `μ[f]` as `∫ (x : Ω), f x ∂μ`.
  1. The two summands of `fun ω => a * X ω + b` must be integrable:
       `fun ω => a * X ω` from `hX`:                                        R1
       `fun ω => b` (a constant; μ is finite):                              R2
  2. Split the integral of the sum, passing those two proofs:               R3
       goal: ∫ a * X ω + ∫ b = a * ∫ X + b       (binders renamed)
  3. Pull the constant factor `a` out of the first integral:                R4
  4. Evaluate the integral of the constant `b`:                             R5 → R6 → R7 → R8
     (`simp` does all four and closes the goal:                             R9)
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem expectation_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (a b : ℝ) :
    μ[fun ω => a * X ω + b] = a * μ[X] + b :=
-- END SPEC
  by
    rw [integral_add (hX.const_mul a) (integrable_const b), integral_const_mul]
    simp

end E096

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split the integral of the sum first (R3); it needs both summands to be integrable, and you can build
    both proofs from `hX` and the constant `b` (R1, R2).
H2. `rw [integral_add h1 h2]` with `h1 : Integrable (fun ω => a * X ω) μ` (from `hX`) and
    `h2 : Integrable (fun ω => b) μ`; then `rw [integral_const_mul]` pulls `a` out, and the integral of the
    constant `b` is `μ.real Set.univ • b = 1 • b = b` (R5–R8, all inside `simp`).
H3. `rw [integral_add (hX.const_mul a) (integrable_const b), integral_const_mul]`, then `simp`.
-/

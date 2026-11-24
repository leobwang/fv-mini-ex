/- E075 | fun_prop | 2 min | fun_prop, Continuous, Differentiable, ContinuousAt, disch, mathlib
GOAL
  Prove continuity and differentiability of functions built from known pieces with `fun_prop`, and pass
  it a discharger when a side condition appears (such as `x ≠ 0` for `Real.log`).
BANNED: continuity

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E075

/- SKELETON · cont_poly
  1. The body is `+` and `*` of `x ^ 2`, `x` and constants. By hand:
       split the sums and the product                                       R2, R3
       close the pieces: constants, `x`, `x ^ 2`                            R4, R5, R6
  2. One tactic applies all of step 1 for you:                              R1
-/
-- BEGIN SPEC
theorem cont_poly : Continuous (fun x : ℝ => x ^ 2 + 3 * x + 1) :=
-- END SPEC
  sorry

/- SKELETON · cont_exp_sin
  1. A product of two named functions:                                      R3
  2. Each factor has a tagged continuity lemma:                             R7
  3. The tactic that chains 1 and 2:                                        R1
-/
-- BEGIN SPEC
theorem cont_exp_sin : Continuous (fun x : ℝ => Real.exp x * Real.sin x) :=
-- END SPEC
  sorry

/- SKELETON · diff_cos_exp
  1. A product (product rule):                                              R9
  2. Each factor is an outer function after an inner one (chain rule):      R10
  3. The pieces `cos`, `exp`, `x ^ 2`, `2 * x`:                              R11 (with R9 for `2 * x`)
  4. The tactic that does 1–3 on a `Differentiable ℝ` goal:                 R8
-/
-- BEGIN SPEC
theorem diff_cos_exp : Differentiable ℝ (fun x : ℝ => Real.cos (x ^ 2) * Real.exp (2 * x)) :=
-- END SPEC
  sorry

/- SKELETON · cont_comb
  1. A sum of a product and a composition:                                  R2, R3, R13
  2. The unknown pieces `f`, `g` are covered by `hf`, `hg` in the context
  3. The tactic that uses those hypotheses as known pieces:                 R12
-/
-- BEGIN SPEC
theorem cont_comb (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x + f (g x)) :=
-- END SPEC
  sorry

/- SKELETON · contAt_log_sin
  1. A product at the single point `2`:                                     R14
  2. The `log` factor leaves a side goal about the point:                   R16 → `⊢ 2 ≠ 0`
     the `sin` factor is continuous everywhere:                             R15 → R7
  3. Plain `fun_prop` stops at that side goal; give it a tactic for it:     R17
-/
-- BEGIN SPEC
theorem contAt_log_sin : ContinuousAt (fun y : ℝ => Real.log y * Real.sin y) 2 :=
-- END SPEC
  sorry

end E075

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every function here is built from continuous/differentiable pieces by `+`, `*` and composition,
    and one tactic (R1) chains the piece lemmas (R2–R7, R9–R11, R13) for you.
H2. `fun_prop` closes the first four directly; in `cont_comb` it uses `hf`, `hg` from the context (R12).
    In `contAt_log_sin` the piece `Real.log` needs the side goal `(2 : ℝ) ≠ 0` (R16), which plain
    `fun_prop` cannot prove: read its error message.
H3. `fun_prop` four times; `fun_prop (disch := norm_num)` for `contAt_log_sin` (R17).
-/

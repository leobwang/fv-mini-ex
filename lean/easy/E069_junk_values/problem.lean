/- E069 | Junk values | 2 min | division by zero, Real.sqrt, Real.log, total functions, mathlib
GOAL
  Mathlib's partial operations are total and return "junk" values (`x / 0 = 0`, `√(-4) = 0`, `log 0 = 0`),
  so honest lemmas such as `x / x = 1` carry side conditions. Find and use those lemmas.
BANNED: simp, simp_all, norm_num, field_simp, grind, try?

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E069

/- SKELETON · real_div_zero
  1. The goal is exactly the junk-value lemma for `/` at argument `x`:          R1
-/
-- BEGIN SPEC
theorem real_div_zero (x : ℝ) : x / 0 = 0 :=
-- END SPEC
  sorry

/- SKELETON · sqrt_neg
  1. Reduce `√(-4) = 0` to the lemma's premise:                                R2
  2. Close the side goal `-4 ≤ 0`:                                              R3
-/
-- BEGIN SPEC
theorem sqrt_neg : Real.sqrt (-4) = 0 :=
-- END SPEC
  sorry

/- SKELETON · log_zero'
  1. The goal is exactly the junk-value lemma for `Real.log`:                   R4
-/
-- BEGIN SPEC
theorem log_zero' : Real.log 0 = 0 :=
-- END SPEC
  sorry

/- SKELETON · div_self'
  1. The honest lemma for `x / x`, with its premise supplied by `hx`:           R5
-/
-- BEGIN SPEC
theorem div_self' (x : ℝ) (hx : x ≠ 0) : x / x = 1 :=
-- END SPEC
  sorry

/- SKELETON · not_div_self
  1. Assume the `∀`; the goal becomes `False`:                                  R6
  2. Use the assumption at the counterexample `x = 0`:  h0 : 0 / 0 = 1        R7
  3. Compute the junk value inside `h0`:                h0 : 0 = 1            R8 (with R1)
  4. Contradict `0 ≠ 1`:                                                        R9
-/
-- BEGIN SPEC
theorem not_div_self : ¬ ∀ x : ℝ, x / x = 1 :=
-- END SPEC
  sorry

end E069

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first four are each one library lemma (R1, R2, R4, R5): match its conclusion with the goal and supply
    any premise. The last one is false at a single point: find it.
H2. `sqrt_neg`: the lemma needs `-4 ≤ 0`, which `linarith` proves. `div_self'`: the premise is `hx`.
    `not_div_self`: `intro` the `∀`, use it at `0`, rewrite `0 / 0` in that hypothesis, contradict `0 ≠ 1`.
H3. `div_zero x`; `Real.sqrt_eq_zero_of_nonpos (by linarith)`; `Real.log_zero`; `div_self hx`;
    `not_div_self`: `intro h; have h0 := h 0; rw [div_zero] at h0; exact zero_ne_one h0`.
-/

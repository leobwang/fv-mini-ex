/- M057 | Solving x² = 4 | 5-10 min | mul_eq_zero, factoring, linarith, mathlib
GOAL
  Solve two quadratic equations over ℝ by factoring and using that a product is zero only if
  a factor is.

BANNED: sq_eq_sq_iff_eq_or_eq_neg, sq_eq_sq', pow_eq_pow_iff_of_ne_zero, sq_eq_sq_iff_abs_eq_abs, mul_self_eq_mul_self_iff

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M057

/- SKELETON · sq_eq_four
  1. The factored form, as a fact (x² - 4 = (x - 2)(x + 2)):                have
       h' : (x - 2) * (x + 2) = 0         proof: R1 → R2 (R2 uses h)
  2. A factor is zero: split h' into two goals                              R3 + R4
       h1 : x - 2 = 0   |   h1 : x + 2 = 0
  3. In each goal (one `·` bullet each): pick the matching side, then
     solve the linear equation h1                                           R5 / R6, then R2
-/
-- BEGIN SPEC
theorem sq_eq_four (x : ℝ) (h : x ^ 2 = 4) : x = 2 ∨ x = -2 :=
-- END SPEC
  by
    have h' : (x - 2) * (x + 2) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith

/- SKELETON · quadratic
  1. Find the roots r, s (r + s = 5, r · s = 6); the factored form as a fact:  have
       h' : (x - r) * (x - s) = 0         proof: R1 → R2 (R2 uses h)
  2. Split h' into the two goals h1 : x - r = 0 | h1 : x - s = 0:              R3 + R4
  3. In each goal: pick the matching side, then solve h1:                      R5 / R6, then R2
-/
-- BEGIN SPEC
theorem quadratic (x : ℝ) (h : x ^ 2 - 5 * x + 6 = 0) : x = 2 ∨ x = 3 :=
-- END SPEC
  by
    have h' : (x - 2) * (x - 3) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith

end M057

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Solve it as in school: write the quadratic as a product of two linear factors, then use that a
    product of reals is zero only if one factor is (`mul_eq_zero`, R3).
H2. First `have h' : (x - 2) * (x + 2) = 0 := by ring_nf; linarith` (R1 expands, R2 uses `h`). Then split
    it with `rcases mul_eq_zero.mp h' with h1 | h1` (R3 + R4) and, in each bullet, pick the side with
    `left` / `right` (R5, R6) and close it with `linarith` (R2). For `quadratic`, factor `x² - 5x + 6`.
H3. `quadratic`: `have h' : (x - 2) * (x - 3) = 0 := by ring_nf; linarith`, then
    `rcases mul_eq_zero.mp h' with h1 | h1`, `· left; linarith`, `· right; linarith`.
-/

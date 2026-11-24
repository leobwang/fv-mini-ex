/- E045 | field_simp | 2-3 min | field_simp, ring, mathlib
GOAL
  Clear denominators in field equations with `field_simp`, then finish with `ring`.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · cancel_x
  1. The only denominator is `x`, and `hx : x ≠ 0` is already in the context.
     Clear it; the polynomial identity left over is closed in the same step:  R1
-/
-- BEGIN SPEC
theorem cancel_x (x : ℝ) (hx : x ≠ 0) : (x ^ 2 + x) / x = x + 1 :=
-- END SPEC
  by field_simp

/- SKELETON · diff_of_squares
  1. The denominator is `x - 1`; state its side condition in the form
     `field_simp` uses, `h : x - 1 ≠ 0`, from `hx : x ≠ 1`:                  R2
  2. Clear the denominator; a polynomial equation is left:                  R3
  3. Close the polynomial identity:                                         R4
-/
-- BEGIN SPEC
theorem diff_of_squares (x : ℝ) (hx : x ≠ 1) : (x ^ 2 - 1) / (x - 1) = x + 1 :=
-- END SPEC
  by
    have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring

/- SKELETON · from_ratio
  1. The division is in the hypothesis `h`, not the goal: clear it there
     (uses `hb : b ≠ 0`); `h` becomes `a = b * 3`:                           R5
  2. The goal follows linearly from `h` (`exact h` fails: `b * 3` vs `3 * b`): R6
-/
-- BEGIN SPEC
theorem from_ratio (a b : ℝ) (hb : b ≠ 0) (h : a / b = 3) : a = 3 * b :=
-- END SPEC
  by
    field_simp at h
    linarith

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `field_simp` clears a denominator `d` only when it can prove `d ≠ 0` from the context. Find each
    denominator and its side condition; in `from_ratio` the division sits in the hypothesis `h`.
H2. `cancel_x`: `field_simp` alone (R1). `diff_of_squares`: first turn `hx` into `x - 1 ≠ 0` (R2), then
    `field_simp` leaves a polynomial identity for `ring` (R3, R4). `from_ratio`: clear `h` (R5); the goal
    then follows linearly from `h` (R6).
H3. `have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx`, then `field_simp` and `ring`. `from_ratio`: `field_simp at h; linarith`.
-/

/- E045 | field_simp | 2-3 min | field_simp, ring, mathlib
GOAL
  Clear denominators in field equations with `field_simp`, then finish with `ring`.

REFERENCE
  example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by field_simp     -- needs `x ≠ 0` in context
  example (a b : ℝ) (hb : b ≠ 0) : a / b * b = a := by field_simp
  example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := by
    field_simp; ring            -- field_simp cross-multiplies; ring closes what is left
  #check sub_ne_zero   -- a - b ≠ 0 ↔ a ≠ b
  `field_simp at h` clears denominators in a hypothesis.
-/
import Mathlib

-- BEGIN SPEC
theorem cancel_x (x : ℝ) (hx : x ≠ 0) : (x ^ 2 + x) / x = x + 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem diff_of_squares (x : ℝ) (hx : x ≠ 1) : (x ^ 2 - 1) / (x - 1) = x + 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem from_ratio (a b : ℝ) (hb : b ≠ 0) (h : a / b = 3) : a = 3 * b :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `field_simp` only clears a denominator `d` if it can see `d ≠ 0`.
H2. `diff_of_squares`: the denominator is `x - 1`; turn `hx` into `x - 1 ≠ 0` first.
H3. `have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx`, then `field_simp` and `ring`. `from_ratio`: `field_simp at h; linarith`.
-/

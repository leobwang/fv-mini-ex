/- M45 | Solving x² = 4 | 5-10 min | mul_eq_zero, factoring, linarith, mathlib
GOAL
  Solve two quadratic equations over ℝ by factoring and using that a product is zero only if
  a factor is.

REFERENCE
  #check mul_eq_zero   -- a * b = 0 ↔ a = 0 ∨ b = 0
  example (x : ℝ) (h : x ^ 2 = 9) : (x - 3) * (x + 3) = 0 := by ring_nf; linarith
    -- `ring_nf` normalises both sides; linarith then uses h
  example (x : ℝ) (h : x - 3 = 0) : x = 3 := by linarith
BANNED: sq_eq_sq_iff_eq_or_eq_neg, sq_eq_sq', pow_eq_pow_iff_of_ne_zero, sq_eq_sq_iff_abs_eq_abs, mul_self_eq_mul_self_iff
-/
import Mathlib

namespace M45

-- BEGIN SPEC
theorem sq_eq_four (x : ℝ) (h : x ^ 2 = 4) : x = 2 ∨ x = -2 :=
-- END SPEC
  by
    have h' : (x - 2) * (x + 2) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith

-- BEGIN SPEC
theorem quadratic (x : ℝ) (h : x ^ 2 - 5 * x + 6 = 0) : x = 2 ∨ x = 3 :=
-- END SPEC
  by
    have h' : (x - 2) * (x - 3) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith

end M45

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Factor the polynomial, then split the product.
H2. `have h' : (x - 2) * (x + 2) = 0 := by ring_nf; linarith`, then `mul_eq_zero.mp h'`.
H3. `rcases mul_eq_zero.mp h' with h1 | h1` and finish each side with `linarith`.
-/

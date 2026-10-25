/- E36 | norm_num | 1-2 min | norm_num, mathlib
GOAL
  Evaluate concrete numeric statements in ℝ, ℚ and ℤ with `norm_num`.

REFERENCE
  example : (2 : ℝ) ^ 5 + 1 = 33 := by norm_num        -- arithmetic with literals
  example : (1 : ℚ) / 3 < 1 / 2 := by norm_num         -- fractions, comparisons
  example : (100 : ℤ) % 7 = 2 := by norm_num           -- div / mod
  example (x : ℝ) (h : x = 3) : x ^ 2 = 9 := by rw [h]; norm_num
  `(5 : ℝ)` fixes the type of a literal; without it Lean defaults to ℕ.
-/
import Mathlib

-- BEGIN SPEC
theorem pow_ten : (2 : ℝ) ^ 10 = 1024 :=
-- END SPEC
  by norm_num

-- BEGIN SPEC
theorem frac_gt : (7 : ℚ) / 2 > 3 :=
-- END SPEC
  by norm_num

-- BEGIN SPEC
theorem big_mod : (12345 : ℤ) % 7 = 4 :=
-- END SPEC
  by norm_num

-- BEGIN SPEC
theorem inv_sum : (3 : ℝ)⁻¹ + 6⁻¹ = 1 / 2 :=
-- END SPEC
  by norm_num

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. No variables appear: everything is a closed numeric fact.
H2. `norm_num` evaluates powers, fractions, inverses and `%` on literals.
H3. Each proof is `norm_num`.
-/

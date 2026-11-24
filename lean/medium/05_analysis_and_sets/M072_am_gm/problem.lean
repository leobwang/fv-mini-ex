/- M072 | AM-GM for two reals | 10 min | nlinarith, sq_nonneg, Real.sqrt, mathlib
GOAL
  Prove the two-variable AM-GM inequality, in squared form and with a square root.

REFERENCE
  example (a b : ℝ) : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  example (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
    -- nlinarith multiplies/combines hypotheses and the hint terms you pass in [..]
  #check Real.sqrt_le_sqrt   -- x ≤ y → √x ≤ √y
  #check Real.sqrt_sq        -- 0 ≤ x → √(x ^ 2) = x
  `rw [show e = e' from proof]` rewrites with a one-off equation.
BANNED: Real.add_pow_le_pow_mul_pow_of_sq_le_sq, Real.inner_le_nnorm_mul_nnorm, Real.geom_mean_le_arith_mean2_weighted, Real.sqrt_mul_self_le, four_mul_le_sq_add
-/
import Mathlib

namespace M072

-- BEGIN SPEC
theorem two_mul_le (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem amgm_sq (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem amgm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 :=
-- END SPEC
  sorry

end M072

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything follows from `0 ≤ (a - b) ^ 2`.
H2. For the root version, write `(a + b) / 2` as `√(((a + b) / 2) ^ 2)` (valid since it is ≥ 0) and use monotonicity of `√`.
H3. `nlinarith [sq_nonneg (a - b)]` twice; then `rw [show (a + b) / 2 = Real.sqrt (((a + b) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]; exact Real.sqrt_le_sqrt (amgm_sq a b)`.
-/

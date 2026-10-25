/- M34 | Bernoulli's inequality | 10-15 min | induction, nlinarith, casts, mathlib
GOAL
  Prove `n + 1 ≤ 2 ^ n`, then Bernoulli's inequality `1 + n x ≤ (1 + x) ^ n` for `x ≥ -1`.

REFERENCE
  example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := mul_le_mul_of_nonneg_right h hc
  example (x : ℝ) (n : ℕ) : 0 ≤ (n : ℝ) * x ^ 2 := by positivity
  -- nlinarith: linarith + products of hypotheses; pass helpful products/squares in [..]
  example (x y : ℝ) (h : 0 ≤ x) (h2 : 0 ≤ y) : 0 ≤ x * y + x := by nlinarith
  example (n : ℕ) : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring   -- move casts inward
  #check pow_succ   -- a ^ (n + 1) = a ^ n * a
BANNED: one_add_mul_le_pow, Nat.lt_two_pow_self, Nat.lt_pow_self, one_add_mul_self_le_pow
-/
import Mathlib

namespace M34

-- BEGIN SPEC
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n :=
-- END SPEC
  sorry

end M34

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both are inductions on `n`; the step multiplies the IH by `2` (resp. `1 + x ≥ 0`).
H2. Bernoulli step: `(1 + x)^(n+1) ≥ (1 + n x)(1 + x) = 1 + (n+1) x + n x² ≥ 1 + (n+1) x`.
H3. `have h2 := mul_le_mul_of_nonneg_right ih h1; push_cast; rw [pow_succ]; nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg x)]`.
-/

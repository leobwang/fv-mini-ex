/- E068 | nlinarith with hints | 2-3 min | nlinarith, product hints, sq_nonneg, mathlib
GOAL
  Prove polynomial inequalities with `nlinarith`, supplying the squares or products it needs as hints.

REFERENCE
  example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  `nlinarith [t₁, t₂]` adds the facts tᵢ, multiplies pairs of hypotheses/hints, then runs `linarith`.
  #check sq_nonneg    -- 0 ≤ a ^ 2
  #check mul_nonneg   -- 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  #check add_nonneg   -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
  Find hints by writing `rhs - lhs` as a sum of (nonnegative factor) × (square) terms.
BANNED: gcongr, pow_lt_pow_left₀, pow_le_pow_iff_left₀, le_of_sq_le_sq, abs_le_of_sq_le_sq, abs_le_of_sq_le_sq', grind, polyrith, exact?, apply?, try?
-/
import Mathlib

namespace E068

-- BEGIN SPEC
theorem nl_sq (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem nl_sym (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 * y + x * y ^ 2 ≤ x ^ 3 + y ^ 3 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem nl_three (a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 :=
-- END SPEC
  sorry

end E068

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Try plain `nlinarith` first; it is enough for `nl_sq`. For the other two, factor `rhs - lhs`.
H2. `x³ + y³ - x²y - xy² = (x + y)(x - y)²`;  `2(a² + b² + c² - ab - bc - ca) = (a - b)² + (b - c)² + (c - a)²`.
H3. `nl_sym`: `nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]`. `nl_three`: one `sq_nonneg` hint
    per square in H2.
-/

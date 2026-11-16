/- E035 | linarith | 2 min | linarith, mathlib
GOAL
  Prove linear (in)equalities over ordered fields from hypotheses with `linarith`.

REFERENCE
  example (x y : ℝ) (h1 : x < y) (h2 : y < 3) : x < 3 := by linarith   -- uses context hyps
  example (a b : ℝ) (h : 2 * a + b = 5) (h2 : b = 1) : a = 2 := by linarith
  example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by linarith [sq_nonneg (a - b)]
    -- extra facts in [..]; nonlinear monomials (a*b, a^2) are treated as atoms
  #check sq_nonneg   -- (a : α) : 0 ≤ a ^ 2
-/
import Mathlib

-- BEGIN SPEC
theorem solve_two (x y : ℝ) (h1 : x + y = 10) (h2 : x - y = 2) : x = 6 := by
-- END SPEC
  linarith

-- BEGIN SPEC
theorem chain_pos (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : 0 < a) : 0 < 2 * c - a := by
-- END SPEC
  linarith

-- BEGIN SPEC
theorem sq_bound (x y : ℝ) : 4 * x * y ≤ (x + y) ^ 2 := by
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two are linear consequences of the hypotheses.
H2. `sq_bound` is not linear, but it is linear in the atoms x², xy, y² once you add the right square.
H3. `linarith`, `linarith`, `linarith [sq_nonneg (x - y)]`.
-/

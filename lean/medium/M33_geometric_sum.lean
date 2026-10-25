/- M33 | Geometric sum | 10 min | Finset.sum, induction, ring, mathlib
GOAL
  Prove the geometric series identities over ℕ (base 2) and over ℝ (any ratio, multiplied out).

REFERENCE
  open Finset in #check sum_range_succ  -- ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n
  #check pow_succ   -- a ^ (n + 1) = a ^ n * a
  example (r s : ℝ) (n : ℕ) (ih : (r - 1) * s = r ^ n - 1) :
      (r - 1) * (s + r ^ n) = r ^ (n + 1) - 1 := by rw [mul_add, ih]; ring
  Stating the ℕ version as `... + 1 = 2 ^ n` avoids truncated subtraction.
BANNED: geom_sum_eq, geom_sum_mul, mul_geom_sum, Nat.geomSum_eq, geom_sum_mul_neg
-/
import Mathlib

open Finset

namespace M33

-- BEGIN SPEC
theorem geom_two (n : ℕ) : ∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem geom_real (r : ℝ) (n : ℕ) : (r - 1) * ∑ i ∈ range n, r ^ i = r ^ n - 1 :=
-- END SPEC
  sorry

end M33

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on `n`, peeling the last term each time.
H2. ℕ: after `sum_range_succ` and `pow_succ` the goal is linear in the atoms `∑ ...` and `2 ^ n`.
H3. `rw [sum_range_succ, pow_succ]; omega` and `rw [sum_range_succ, mul_add, ih]; ring`.
-/

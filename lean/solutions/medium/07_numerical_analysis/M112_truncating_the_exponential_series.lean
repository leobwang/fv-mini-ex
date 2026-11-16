/- M112 | Truncating the exponential series | 5-10 min | Real.exp_bound, Finset.sum_range_succ, norm_num, mathlib
GOAL
  Certify a numerical value: the truncated series `1 + 1/2 + (1/2)²/2 = 13/8` approximates `e^{1/2}`
  within `1/36`, using Mathlib's explicit remainder bound. Then derive the decimal bounds `1.59 < e^{1/2} < 1.66`.

REFERENCE
  `∑ m ∈ Finset.range n, f m` is `f 0 + … + f (n-1)`;  `m.factorial` (written `m !` after `open Nat`) is m factorial.
  #check Real.exp_bound   -- |x| ≤ 1 → 0 < n → |exp x - ∑ m ∈ range n, x ^ m / m!| ≤ |x| ^ n * (n.succ / (n! * n))
  example : |(1 / 2 : ℝ)| ≤ 1 := by norm_num [abs_of_pos]
  example (x : ℝ) (hx : |x| ≤ 1) := Real.exp_bound hx (n := 5) (by norm_num)   -- choose n by a named argument
  #check Finset.sum_range_succ  -- ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n
  example : ∑ m ∈ Finset.range 3, (2 : ℝ) ^ m = 7 := by norm_num [Finset.sum_range_succ]
  example : (3 : ℕ).factorial = 6 := by norm_num [Nat.factorial]
  #check abs_le           -- |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
  `norm_num [lemmas] at h ⊢` simplifies numerals in `h` and the goal; decimals like `1.59` are exact rationals.
BANNED: exp_one_gt_d9, exp_one_lt_d9, exp_one_near_10, exp_one_near_20, exp_half
-/
import Mathlib

namespace M112

-- BEGIN SPEC
theorem exp_half_approx : |Real.exp (1 / 2) - 13 / 8| ≤ 1 / 36 :=
-- END SPEC
  by
    have h := Real.exp_bound (x := 1 / 2) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith

-- BEGIN SPEC
theorem exp_half_bounds : 1.59 < Real.exp (1 / 2) ∧ Real.exp (1 / 2) < 1.66 :=
-- END SPEC
  by
    have h := abs_le.mp exp_half_approx
    constructor <;> norm_num <;> linarith [h.1, h.2]

end M112

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `13/8` is the sum of the first three terms of `∑ xᵐ/m!` at `x = 1/2`, so use `Real.exp_bound` with `n = 3`.
H2. Instantiate the bound, then let `norm_num` expand the finite sum and the factorials in it; the
    remainder constant `(1/2)³ · 4/(3!·3)` simplifies to `1/36`.
H3. `have h := Real.exp_bound (x := 1 / 2) _ (n := 3) _`, then let `norm_num` expand the 3-term sum and the
    factorials in `h`; the goal follows by linear arithmetic. Bounds: unfold `|·| ≤` with `abs_le`.
-/

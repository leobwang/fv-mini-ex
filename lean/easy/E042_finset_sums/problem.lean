/- E042 | Finset sums | 3 min | Finset.sum, Finset.range, sum_range_succ, mathlib
GOAL
  Manipulate finite sums `∑ i ∈ Finset.range n, f i` (= f 0 + … + f (n-1)).

REFERENCE
  open Finset in example : ∑ i ∈ range 4, i = 6 := by decide    -- small closed sums compute
  #check Finset.sum_range_succ  -- ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n
  #check Finset.sum_add_distrib -- ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i
  #check Finset.mul_sum         -- b * ∑ i ∈ s, f i = ∑ i ∈ s, b * f i
  `∑` is typed `\sum`; `open Finset` lets you write `range` for `Finset.range`.
-/
import Mathlib

open Finset

-- BEGIN SPEC
theorem sum_squares_five : ∑ i ∈ range 5, i ^ 2 = 30 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem peel_two (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range (n + 2), f i = (∑ i ∈ range n, f i) + f n + f (n + 1) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sum_linear (f g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range n, (f i + 2 * g i) = ∑ i ∈ range n, f i + 2 * ∑ i ∈ range n, g i :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `sum_range_succ` peels off the last term of a sum over `range (n + 1)`.
H2. `peel_two`: `n + 2 = (n + 1) + 1`, so peel twice. `sum_linear`: split the sum, then pull out the 2.
H3. `simp [sum_range_succ]` (or `decide`); `rw [sum_range_succ, sum_range_succ]`; `rw [sum_add_distrib, mul_sum]`.
-/

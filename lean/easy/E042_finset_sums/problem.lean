/- E042 | Finset sums | 3 min | Finset.sum, Finset.range, sum_range_succ, mathlib
GOAL
  Manipulate finite sums `∑ i ∈ Finset.range n, f i` (= f 0 + … + f (n-1)).

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Finset

/- SKELETON · sum_squares_five
  1. Unroll the sum over `range 5` into its five terms; `simp` peels the last term
     repeatedly (R2 on each numeral 5, 4, …, 1), drops the empty sum (R3) and does the
     arithmetic, which closes the goal:                                    R4
     (Alternative: the sum is a closed computation, so `decide` works too.)
-/
-- BEGIN SPEC
theorem sum_squares_five : ∑ i ∈ range 5, i ^ 2 = 30 :=
-- END SPEC
  sorry

/- SKELETON · peel_two
  1. Peel the last term off `range (n + 2)`; no rewrite of `n + 2` is needed:  R2
  2. Peel the last term off the `range (n + 1)` that appears:                 R1
  3. Both sides are now the same; `rw` closes the goal with `rfl` by itself.
-/
-- BEGIN SPEC
theorem peel_two (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range (n + 2), f i = (∑ i ∈ range n, f i) + f n + f (n + 1) :=
-- END SPEC
  sorry

/- SKELETON · sum_linear
  1. Split the sum of `f i + 2 * g i` into two sums:                          R5
  2. The goal has `∑ x ∈ range n, 2 * g x` on the left and `2 * ∑ i ∈ range n, g i`
     on the right: rewrite one into the other; `rw` then closes the goal
     with `rfl`:                                                              R6
-/
-- BEGIN SPEC
theorem sum_linear (f g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range n, (f i + 2 * g i) = ∑ i ∈ range n, f i + 2 * ∑ i ∈ range n, g i :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything here is `Finset.sum_range_succ` (peel the last term off a sum over `range (n + 1)`) and
    linearity of `∑`: a sum of `+` splits, a constant factor moves in and out.
H2. `sum_squares_five`: unroll the whole sum with `simp` given the peeling lemma (R4); `decide` also works.
    `peel_two`: `rw` reads `range (n + 2)` as `range ((n + 1) + 1)`, so peel twice (R2, then R1).
    `sum_linear`: split with `sum_add_distrib` (R5), then match `2 * ∑ g` with `∑ 2 * g` (R6).
H3. `simp [sum_range_succ]`; `rw [sum_range_succ, sum_range_succ]`; `rw [sum_add_distrib, mul_sum]`.
-/

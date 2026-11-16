/- M051 | Gauss sum | 5-10 min | Finset.sum, induction, sum_range_succ, ring, mathlib
GOAL
  Prove the closed forms for 0 + 1 + … + n and for the sum of the first n odd numbers.

REFERENCE
  open Finset in #check sum_range_succ  -- ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n
  example (n : ℕ) (s : ℕ) (ih : 2 * s = n * (n + 1)) : 2 * (s + (n + 1)) = (n + 1) * (n + 2) := by
    rw [mul_add, ih]; ring        -- rewrite with the IH, then ring
  #check mul_add   -- a * (b + c) = a * b + a * c
  Induct on `n`; in the step, peel the last term with `sum_range_succ`.
BANNED: Finset.sum_range_id_mul_two, Finset.sum_range_id, Gauss_sum, Finset.sum_range_succ_mul_comm
-/
import Mathlib

open Finset

namespace M051

-- BEGIN SPEC
theorem gauss (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 :=
-- END SPEC
  sorry

end M051

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both are inductions on `n` where the step adds one term.
H2. `rw [sum_range_succ]` exposes `(∑ ... ) + f n`; then use the IH and close with `ring`.
H3. `gauss` step: `rw [sum_range_succ, mul_add, ih]; ring`. `sum_odd` step: `rw [sum_range_succ, ih]; ring`.
-/

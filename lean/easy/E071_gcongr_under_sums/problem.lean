/- E071 | gcongr under sums | 2 min | gcongr with, Finset.sum, Finset.prod, monotonicity, mathlib
GOAL
  Compare two sums (or products) over the same index set term by term with `gcongr`.

REFERENCE
  example (f g : ℕ → ℝ) (s : Finset ℕ) (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, 2 * f i ≤ ∑ i ∈ s, 2 * g i := by gcongr with i hi; exact h i hi
  `gcongr with i hi` names the bound index `i` and its membership proof `hi : i ∈ s`, and leaves
  the goal for one term (here `f i ≤ g i`). Products of natural numbers work the same way.
  #check Finset.mem_range   -- m ∈ range n ↔ m < n
  example (x : ℝ) (h : 1 ≤ x) : x ≤ x ^ 2 := by nlinarith
BANNED: Finset.sum_le_sum, Finset.prod_le_prod, Finset.prod_le_prod', exact?
-/
import Mathlib

namespace E071

-- BEGIN SPEC
open Finset

theorem sum_mono (f g : ℕ → ℝ) (n : ℕ) (h : ∀ i, f i ≤ g i) :
    ∑ i ∈ range n, f i ≤ ∑ i ∈ range n, g i :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sum_le_sq (f : ℕ → ℝ) (n : ℕ) (h : ∀ i ∈ range n, 1 ≤ f i) :
    ∑ i ∈ range n, f i ≤ ∑ i ∈ range n, f i ^ 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem prod_mono (f g : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, f i ≤ g i) :
    ∏ i ∈ range n, f i ≤ ∏ i ∈ range n, g i :=
-- END SPEC
  sorry

end E071

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides are a sum (product) over the same `range n`; only the terms differ.
H2. `gcongr with i hi` leaves one term-wise goal with `hi : i ∈ range n` in context. Fit each `h` to it:
    `sum_le_sq` needs a little algebra, `prod_mono` needs `i < n` from `hi`.
H3. `exact h i`; `have := h i hi` then `nlinarith`; `exact h i (mem_range.mp hi)`.
-/

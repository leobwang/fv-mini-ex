/- E071 | gcongr under sums | 2 min | gcongr with, Finset.sum, Finset.prod, monotonicity, mathlib
GOAL
  Compare two sums (or products) over the same index set term by term with `gcongr`.
BANNED: Finset.sum_le_sum, Finset.prod_le_prod, Finset.prod_le_prod', exact?

GUIDE
  Entries R1–R5: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E071

/- SKELETON · sum_mono
  1. Same index set on both sides: reduce to one term,
       i : ℕ, hi : i ∈ range n ⊢ f i ≤ g i                                      R1
  2. The term goal is `h` at that index (`h` has no membership premise):         R2
-/
-- BEGIN SPEC
open Finset

theorem sum_mono (f g : ℕ → ℝ) (n : ℕ) (h : ∀ i, f i ≤ g i) :
    ∑ i ∈ range n, f i ≤ ∑ i ∈ range n, g i :=
-- END SPEC
  sorry

/- SKELETON · sum_le_sq
  1. Reduce to one term:  hi : i ∈ range n ⊢ f i ≤ f i ^ 2                       R1
  2. Bring `1 ≤ f i` into the context (`h` needs `i` and `hi`):                  R2
  3. Close the nonlinear inequality from that fact:                              R3
-/
-- BEGIN SPEC
theorem sum_le_sq (f : ℕ → ℝ) (n : ℕ) (h : ∀ i ∈ range n, 1 ≤ f i) :
    ∑ i ∈ range n, f i ≤ ∑ i ∈ range n, f i ^ 2 :=
-- END SPEC
  sorry

/- SKELETON · prod_mono
  1. Reduce to one factor (side goals `0 ≤ f i` are automatic in ℕ):
       hi : i ∈ range n ⊢ f i ≤ g i                                              R4
  2. `h` wants `i < n`, not `i ∈ range n`: translate `hi`, then apply `h`:      R5 → R2
-/
-- BEGIN SPEC
theorem prod_mono (f g : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, f i ≤ g i) :
    ∏ i ∈ range n, f i ≤ ∏ i ∈ range n, g i :=
-- END SPEC
  sorry

end E071

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides are a sum (product) over the same `range n`; only the terms differ. `gcongr` reduces such a
    goal to one term-wise goal; name the index and its membership proof.
H2. `gcongr with i hi` leaves `hi : i ∈ range n ⊢ (term) ≤ (term)`. Then fit `h` to that goal:
    `sum_mono` uses `h i` directly; `sum_le_sq` needs `h i hi` in the context and then `nlinarith`;
    `prod_mono` needs `i < n`, which `Finset.mem_range` turns `hi` into.
H3. `exact h i`;  `have := h i hi` then `nlinarith`;  `exact h i (mem_range.mp hi)`.
-/

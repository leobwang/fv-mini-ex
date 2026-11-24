/- M051 | Gauss sum | 5-10 min | Finset.sum, induction, sum_range_succ, ring, mathlib
GOAL
  Prove the closed forms for 0 + 1 + … + n and for the sum of the first n odd numbers.
BANNED: Finset.sum_range_id_mul_two, Finset.sum_range_id, Gauss_sum, Finset.sum_range_succ_mul_comm

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Finset

namespace M051

/- SKELETON · gauss
  1. Induct on `n`:                                                         R1
  2. `zero`: a one-term sum and numerals:                                   R4 (by hand: R3)
  3. `succ`: peel off the last term `n + 1`                                 R5
       distribute the `2` so the IH's left side `2 * ∑ …` appears          R6
       replace it by `n * (n + 1)`                                         R7 (rw [ih])
       the rest is a polynomial identity                                   R8
-/
-- BEGIN SPEC
theorem gauss (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, mul_add, ih]
      ring

/- SKELETON · sum_odd
  1. Induct on `n`:                                                         R1
  2. `zero`: the empty sum:                                                 R4 (by hand: R2)
  3. `succ`: peel off the last term `2 * n + 1`                             R5
       the IH's left side is already there; replace it by `n ^ 2`          R7 (rw [ih])
       the rest is a polynomial identity                                   R8
-/
-- BEGIN SPEC
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      ring

end M051

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both are inductions on `n` where the `succ` step adds one term to the sum; `zero` is a sum of at most
    one term, which `simp` closes.
H2. In the `succ` step peel off the last term with `rw [Finset.sum_range_succ]`, make the induction
    hypothesis's left side appear (for `gauss`, distribute the `2` with `mul_add`), `rw [ih]`, then `ring`.
H3. `gauss` step: `rw [sum_range_succ, mul_add, ih]; ring`. `sum_odd` step: `rw [sum_range_succ, ih]; ring`.
-/

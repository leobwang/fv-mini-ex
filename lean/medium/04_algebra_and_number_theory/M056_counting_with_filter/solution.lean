/- M056 | Counting with Finset.filter | 15 min | Finset.filter, Finset.card, induction, mathlib
GOAL
  Exactly `n` of the numbers `0, 1, …, 2n - 1` are even.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Finset

namespace M056

/- SKELETON · even_count
  1. Induct on `n`:                                                         R1
  2. `zero`: the empty range, nothing to count:                            R2
  3. `succ`: reshape `2 * (n + 1)` as `2 * n + 1 + 1`                       R3
       expose the two new numbers: `range` → `insert (2n+1) (insert (2n) …)` R4, R4
       push the filter through both `insert`s (nested `if`s appear)        R5, R5
       the parity facts, as `have`s:
         h1 : ¬ Even (2 * n + 1)                                           R7
         h2 : Even (2 * n)                                                 R6
       resolve the `if`s with h1, h2                                       R8, R9
       count the one inserted element; side goal `2 * n ∉ …`              R10
         close the side goal inline with `(by simp)`                       R13 (= R11, R12)
       replace the count of `filter Even (range (2 * n))`                  rw [ih]
         (`rw` then closes `n + 1 = n + 1` by `rfl` itself)
-/
-- BEGIN SPEC
theorem even_count (n : ℕ) : ((range (2 * n)).filter Even).card = n :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, range_add_one, range_add_one,
        filter_insert, filter_insert]
      have h1 : ¬ Even (2 * n + 1) := by simp
      have h2 : Even (2 * n) := even_two_mul n
      simp only [h1, h2, if_true, if_false]
      rw [card_insert_of_notMem (by simp), ih]

end M056

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on `n`: going from `2n` to `2n + 2` adds the numbers `2n` (even, counted) and `2n + 1` (odd, not
    counted). The `zero` case is `simp`.
H2. In `succ`, rewrite `range (2 * (n + 1))` as `insert (2n+1) (insert (2n) (range (2n)))` (R3, R4 twice), push
    the filter through both inserts (R5 twice), resolve the parity `if`s (R6–R9), then count with
    `card_insert_of_notMem` (R10) and finish with `ih`.
H3. `rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, range_add_one, range_add_one, filter_insert, filter_insert]`,
    then `simp only [h1, h2, if_true, if_false]` with the two parity facts, then
    `rw [card_insert_of_notMem (by simp), ih]`.
-/

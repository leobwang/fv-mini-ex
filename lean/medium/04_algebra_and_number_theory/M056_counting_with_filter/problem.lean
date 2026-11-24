/- M056 | Counting with Finset.filter | 15 min | Finset.filter, Finset.card, induction, mathlib
GOAL
  Exactly `n` of the numbers `0, 1, …, 2n - 1` are even.

REFERENCE
  open Finset in #check range_add_one   -- range (n + 1) = insert n (range n)
  #check Finset.filter_insert           -- filter p (insert a s) = if p a then insert a (filter p s) else filter p s
  #check Finset.card_insert_of_notMem   -- a ∉ s → #(insert a s) = #s + 1
  example (n : ℕ) : Even (2 * n) := even_two_mul n
  example (n : ℕ) : ¬ Even (2 * n + 1) := by simp
  example (n : ℕ) : 2 * n ∉ Finset.filter Even (Finset.range (2 * n)) := by simp
-/
import Mathlib

open Finset

namespace M056

-- BEGIN SPEC
theorem even_count (n : ℕ) : ((range (2 * n)).filter Even).card = n :=
-- END SPEC
  sorry

end M056

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on `n`: going from `2n` to `2n + 2` adds the numbers `2n` (even) and `2n + 1` (odd).
H2. Rewrite `range (2n + 2)` as `insert (2n+1) (insert (2n) (range (2n)))`, push the filter through both inserts.
H3. `rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, range_add_one, range_add_one, filter_insert, filter_insert]`, simplify the parity `if`s, then `rw [card_insert_of_notMem (by simp), ih]`.
-/

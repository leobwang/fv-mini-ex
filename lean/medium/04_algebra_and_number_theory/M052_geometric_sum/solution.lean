/- M052 | Geometric sum | 10 min | Finset.sum, induction, ring, mathlib
GOAL
  Prove the geometric series identities over ℕ (base 2) and over ℝ (any ratio, multiplied out).
BANNED: geom_sum_eq, geom_sum_mul, mul_geom_sum, Nat.geomSum_eq, geom_sum_mul_neg

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Finset

namespace M052

/- SKELETON · geom_two
  1. Induct on `n`, leaving both cases open:                                R1
  2. `zero`: the empty sum is 0 and `2 ^ 0 = 1`; `simp` closes it          R2, R3 (inside `simp`)
  3. `succ`: peel the last term off the sum, then unfold the power:         R4 → R5
       the goal is now linear in the atoms `∑ x ∈ range n, 2 ^ x` and `2 ^ n`,
       and `ih` relates the same two atoms
  4. Close with linear arithmetic over ℕ (it uses `ih` from the context):   R6
-/
-- BEGIN SPEC
theorem geom_two (n : ℕ) : ∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, pow_succ]
      omega

/- SKELETON · geom_real
  1. Induct on `n`, leaving both cases open:                                R1
  2. `zero`: empty sum, `r ^ 0 = 1`, then `a * 0 = 0`, `1 - 1 = 0`; `simp`  R2, R3 (inside `simp`)
  3. `succ`: peel the last term off the sum:                                R4
  4. Distribute `(r - 1) * (… + …)` so that the left side of `ih`
     appears literally, then substitute it:                                 R7 → rw [ih]
  5. Close the remaining identity in `r`, `r ^ n`:                          R8
-/
-- BEGIN SPEC
theorem geom_real (r : ℝ) (n : ℕ) : (r - 1) * ∑ i ∈ range n, r ^ i = r ^ n - 1 :=
-- END SPEC
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, mul_add, ih]
      ring

end M052

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on `n` (R1); each step peels the last term off the sum with `sum_range_succ` (R4).
H2. ℕ: after R4 and `pow_succ` (R5) the goal is linear in the atoms `∑ …` and `2 ^ n`, so `omega` (R6)
    finishes with `ih`. ℝ: after R4 distribute with `mul_add` (R7) so `ih` can be rewritten, then `ring` (R8).
    Both base cases: `simp`.
H3. `rw [sum_range_succ, pow_succ]; omega` and `rw [sum_range_succ, mul_add, ih]; ring`.
-/

/- E089 | Induction from a base | 3-5 min | Nat.le_induction, induction using, calc, mathlib
GOAL
  Prove two inequalities that hold only from some `n₀` on (`3` and `4`), by an induction that
  starts at `n₀` instead of at `0`.
BANNED: grind, exact?, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E089

/- SKELETON · lin_ge
  1. Induct from the base 3, using `hn : 3 ≤ n`; cases `base` and `succ k hk ih`:      R1
  2. `base`: a goal of numerals only:                                                   R2
  3. `succ`: peel one factor `2` off `2 ^ (k + 1)` so the `2 ^ k` of `ih` appears:      R3
     then the goal is linear in `k` and the atom `2 ^ k`; close it from `ih`:           R4
-/
-- BEGIN SPEC
theorem lin_ge (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n :=
-- END SPEC
  by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega

/- SKELETON · pow_ge_sq
  1. Induct from the base 4, using `hn : 4 ≤ n`:                                        R1
  2. `base`: a goal of numerals only:                                                   R2
  3. `succ`: first the non-linear helper (needs `hk : 4 ≤ k`):                          have, R5
       h : 2 * k + 1 ≤ k ^ 2
  4. Then a three-link chain from `(k + 1) ^ 2` to `2 ^ (k + 1)`:                     R6
       `=` expand the square into `k ^ 2 + (2 * k + 1)`                                 R7
       `≤` bound both parts by `2 ^ k`, from `ih` and `h` (atoms `k ^ 2`, `2 ^ k`)       R4
       `=` collect `2 ^ k + 2 ^ k` into `2 ^ (k + 1)`                                   R7
-/
-- BEGIN SPEC
theorem pow_ge_sq (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n :=
-- END SPEC
  by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have h : 2 * k + 1 ≤ k ^ 2 := by nlinarith
      calc (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by ring

end E089

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both fail for small `n` (try `n = 2` and `n = 3`), so a plain `induction n` from `0` has a false
    step: induct from the base with `Nat.le_induction` (R1). The base cases are numerals (R2).
H2. In each step, relate `2 ^ (k + 1)` to the `2 ^ k` of `ih`. For `lin_ge` that is one rewrite (R3) and
    linear arithmetic (R4). For `pow_ge_sq`, `(k + 1) ^ 2 = k ^ 2 + (2 * k + 1)`: bound `k ^ 2` by `ih`
    and `2 * k + 1` by a helper `2 * k + 1 ≤ k ^ 2` (true since `k ≥ 4`), proved by `nlinarith` (R5).
H3. `induction n, hn using Nat.le_induction with | base => norm_num | succ k hk ih => …`.
    `lin_ge` step: `rw [pow_succ]` then `omega`. `pow_ge_sq` step: `have h : 2 * k + 1 ≤ k ^ 2 := by nlinarith`,
    then `calc (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := …` via `_ ≤ 2 ^ k + 2 ^ k` to `_ = 2 ^ (k + 1)`,
    the links by `ring`, `omega`, `ring`.
-/

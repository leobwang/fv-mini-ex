/- E089 | Induction from a base | 3-5 min | Nat.le_induction, induction using, calc, mathlib
GOAL
  Prove two inequalities that hold only from some `n₀` on (`3` and `4`), by an induction that
  starts at `n₀` instead of at `0`.

REFERENCE
  -- for a goal with `hn : n₀ ≤ n`, induct from n₀ (base case n = n₀, step k → k + 1):
  example (n : ℕ) (hn : 1 ≤ n) : n ≤ n ^ 2 := by
    induction n, hn using Nat.le_induction with
    | base => norm_num                 -- goal at n = 1
    | succ k hk ih => nlinarith        -- hk : 1 ≤ k, ih : k ≤ k ^ 2, goal: k + 1 ≤ (k + 1) ^ 2
  #check Nat.le_induction  -- the induction principle behind `using`
  #check pow_succ          -- a ^ (n + 1) = a ^ n * a
  -- `calc` chains `=`/`≤` steps; `nlinarith` proves polynomial inequalities from hypotheses
BANNED: grind, exact?, try?
-/
import Mathlib

namespace E089

-- BEGIN SPEC
theorem lin_ge (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem pow_ge_sq (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n :=
-- END SPEC
  sorry

end E089

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both fail for small `n` (try `n = 2` and `n = 3`), so plain `induction n` cannot work.
H2. Use the card's `induction n, hn using Nat.le_induction with` shape. The base cases are numerals.
    In the step, rewrite `2 ^ (k + 1)` as `2 ^ k * 2`; for `pow_ge_sq`, first prove the helper
    `2 * k + 1 ≤ k ^ 2` (true since `k ≥ 4`) with `nlinarith`.
H3. `lin_ge` step: `rw [pow_succ]; omega`. `pow_ge_sq` step:
    `calc (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
       _ ≤ 2 ^ k + 2 ^ k := by omega
       _ = 2 ^ (k + 1) := by ring`.
-/

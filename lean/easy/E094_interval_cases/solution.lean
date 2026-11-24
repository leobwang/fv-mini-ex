/- E094 | interval_cases | 2 min | interval_cases, bounded case split, mathlib
GOAL
  A variable pinned between two bounds takes finitely many values: split into one goal per value
  with `interval_cases`, then close each concrete goal.

REFERENCE
  example (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 3) : n * n ≤ 9 := by interval_cases n <;> norm_num
    -- reads the bounds on `n` from the context; one goal per value n = 1, 2, 3
  example (n : ℕ) (h : n < 3) : n ^ 2 ≠ 5 := by interval_cases n <;> norm_num  -- ℕ: 0 is the free lower bound
  example (x : ℤ) (h1 : -1 ≤ x) (h2 : x < 2) (h : x * x = 1) : x ≠ 0 := by interval_cases x <;> simp_all
    -- ℤ needs both bounds (`≤` or `<`); the value is substituted into hypotheses too, so a branch
    -- whose hypothesis became false (`0 * 0 = 1`) closes with `simp_all`
BANNED: decide, of_decide_eq_true, decide_eq_true_iff, decide_eq_true_eq, nlinarith, grind, try?
NOTE: E031 did this split by hand (`have : n = 0 ∨ n = 1 := by omega; rcases this with rfl | rfl`).
  `decide` and its lemma forms are banned because `revert h; revert n; decide` checks every value
  without `interval_cases`; finish branches with `norm_num` / `simp_all` instead.
-/
import Mathlib

namespace E094

-- BEGIN SPEC
theorem ic_sq (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 5) (h3 : n ^ 2 = 16) : n = 4 :=
-- END SPEC
  by interval_cases n <;> simp_all

-- BEGIN SPEC
theorem ic_cube (n : ℕ) (h : n < 4) : n ^ 3 < 30 :=
-- END SPEC
  by interval_cases n <;> norm_num

-- BEGIN SPEC
theorem ic_int (x : ℤ) (h1 : -2 ≤ x) (h2 : x < 3) (h : x ^ 3 - x = 0) : x = -1 ∨ x = 0 ∨ x = 1 :=
-- END SPEC
  -- WHY: `-2 ≤ x` matters: unlike ℕ, ℤ has no built-in lower bound for `interval_cases`.
  by interval_cases x <;> simp_all

end E094

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each variable has a lower and an upper bound in the context (for `ic_cube` the lower bound is `0 ≤ n`, built into ℕ).
H2. `interval_cases n` leaves one goal per value with `n` replaced by a literal everywhere; finish all of them with `<;>`.
H3. `ic_sq`: `interval_cases n <;> simp_all` (a false hypothesis like `3 ^ 2 = 16` kills its branch).
    The other two follow the same pattern: `simp_all` when a hypothesis must become false, `norm_num` when
    only the goal is concrete. Avoid `norm_num at h ⊢`: on a branch where `h` already closed the goal,
    the `⊢` part fails with "No goals to be solved".
-/

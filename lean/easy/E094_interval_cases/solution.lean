/- E094 | interval_cases | 2 min | interval_cases, bounded case split, mathlib
GOAL
  A variable pinned between two bounds takes finitely many values: split into one goal per value
  with `interval_cases`, then close each concrete goal.
BANNED: decide, of_decide_eq_true, decide_eq_true_iff, decide_eq_true_eq, nlinarith, grind, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E094

/- SKELETON · ic_sq
  1. Split `n` into 2, 3, 4, 5 (bounds `h1`, `h2`); `n` is replaced in `h3` too:             R1
  2. Finish all four branches with one tactic:                                              R2
  3. Branches 2, 3, 5: `h3` became a false numeral equation (e.g. `3 ^ 2 = 16`);
     branch 4: the goal is `4 = 4`. The same closer handles both:                           R3, R4
-/
-- BEGIN SPEC
theorem ic_sq (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 5) (h3 : n ^ 2 = 16) : n = 4 :=
-- END SPEC
  by interval_cases n <;> simp_all

/- SKELETON · ic_cube
  1. Split `n` into 0, 1, 2, 3; the lower bound `0` is built into ℕ:                        R5
  2. Finish all four branches with one tactic:                                              R2
  3. Each branch is a true inequality between literals (`3 ^ 3 < 30`):                      R6
-/
-- BEGIN SPEC
theorem ic_cube (n : ℕ) (h : n < 4) : n ^ 3 < 30 :=
-- END SPEC
  by interval_cases n <;> norm_num

/- SKELETON · ic_int
  1. Split `x` into -2, -1, 0, 1, 2; on ℤ both `h1` and `h2` are needed:                    R7
  2. Finish all five branches with one tactic:                                              R2
  3. Branches -2, 2: `h` became false (`h : (-2) ^ 3 - -2 = 0` is `-6 = 0`; `2 ^ 3 - 2 = 0`
     is `6 = 0`); branches -1, 0, 1: `h` is true and the disjunction is a true literal
     statement (`⊢ 0 = -1 ∨ 0 = 0 ∨ 0 = 1`). The same closer handles both:                 R3, R4
-/
-- BEGIN SPEC
theorem ic_int (x : ℤ) (h1 : -2 ≤ x) (h2 : x < 3) (h : x ^ 3 - x = 0) : x = -1 ∨ x = 0 ∨ x = 1 :=
-- END SPEC
  -- WHY: `-2 ≤ x` matters: unlike ℕ, ℤ has no built-in lower bound for `interval_cases`.
  by interval_cases x <;> simp_all

end E094

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each variable has a lower and an upper bound in the context (for `ic_cube` the lower bound `0 ≤ n` is
    built into ℕ), so it takes finitely many values. Split on them; every branch is then about literals.
H2. `interval_cases` (R1, R5, R7) leaves one goal per value with the variable replaced everywhere; close all
    branches at once with `<;>` (R2). Where a substituted hypothesis is false, or the goal is a true literal
    equation, use `simp_all` (R3, R4); where only the goal is a concrete inequality, `norm_num` (R6).
H3. `ic_sq`: `interval_cases n <;> simp_all`. `ic_cube`: the same split, finished with `norm_num`.
    `ic_int`: split `x`, finish with `simp_all`. Avoid `norm_num at h ⊢`: on a branch where `h` already
    closed the goal, the `⊢` part fails with "No goals to be solved".
-/

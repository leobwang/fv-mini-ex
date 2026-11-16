/- E041 | use and push Not | 2-3 min | use, push Not, push_neg, mathlib
GOAL
  Give witnesses with `use` and move negations inward with `push Not`.

REFERENCE
  example : ∃ n : ℕ, n * n = 16 := by use 4            -- `use` gives the witness, tries rfl
  example : ∃ a b : ℕ, a + b = 3 := by use 1, 2         -- several witnesses at once
  example : ¬ ∀ n : ℕ, n ≤ 3 := by push Not; use 4; norm_num  -- goal was ∃ n, 3 < n
  example (f : ℕ → ℕ) (h : ¬ ∃ n, f n = 0) : ∀ n, f n ≠ 0 := by push Not at h; exact h
  `push_neg` is the older name of `push Not` (still works, with a deprecation warning).
-/
import Mathlib

-- BEGIN SPEC
theorem not_all_small : ¬ ∀ n : ℕ, n < 5 :=
-- END SPEC
  by
    push Not
    use 5

-- BEGIN SPEC
theorem exists_pair : ∃ a b : ℕ, a + b = 7 ∧ a * b = 12 :=
-- END SPEC
  by use 3, 4

-- BEGIN SPEC
theorem unbounded (f : ℕ → ℕ) (hf : ∀ n, f n = 2 * n) : ¬ ∃ M, ∀ n, f n ≤ M :=
-- END SPEC
  by
    push Not
    intro M
    use M + 1
    rw [hf]
    omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `push Not` turns `¬ ∀` into `∃ ¬` and `¬ ∃` into `∀ ¬`, and `¬ (a ≤ b)` into `b < a`.
H2. `unbounded`: after `push Not` the goal is `∀ M, ∃ n, M < f n`.
H3. `push Not; intro M; use M + 1; rw [hf]; omega`.
-/

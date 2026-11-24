/- E041 | use and push Not | 2-3 min | use, push Not, push_neg, mathlib
GOAL
  Give witnesses with `use` and move negations inward with `push Not`.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · not_all_small
  1. Push the negation in: `¬ ∀ n` becomes `∃ n`, and `¬ (n < 5)` becomes `≤`:  R1, R2
  2. Give the witness that makes the `≤` read `a ≤ a`; `use` then closes it:   R6, R7
       (a larger witness leaves `5 ≤ k`, which `omega` closes: R12)
-/
-- BEGIN SPEC
theorem not_all_small : ¬ ∀ n : ℕ, n < 5 :=
-- END SPEC
  sorry

/- SKELETON · exists_pair
  1. Find `a, b` on paper: sum 7, product 12.
  2. Give both witnesses; `use` checks both conjuncts by evaluation:            R8, R9
-/
-- BEGIN SPEC
theorem exists_pair : ∃ a b : ℕ, a + b = 7 ∧ a * b = 12 :=
-- END SPEC
  sorry

/- SKELETON · unbounded
  1. Push the negation through `∃ M`, `∀ n` and the `≤`, in one call:           R4, R5, R3
       the goal becomes `∀ M, ∃ n, M < f n`
  2. Introduce the bound `M`:                                                   R10
  3. Choose `n` as an expression in `M` with `M < 2 * n` for EVERY `M`:         R6
  4. Replace `f n` by its formula:                                              R11
  5. Close the linear inequality over `ℕ`:                                      R12
-/
-- BEGIN SPEC
theorem unbounded (f : ℕ → ℕ) (hf : ∀ n, f n = 2 * n) : ¬ ∃ M, ∀ n, f n ≤ M :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each goal starts with `¬` in front of a quantifier, or with `∃`. `push Not` turns `¬ ∀` into `∃ ¬`,
    `¬ ∃` into `∀ ¬`, `¬ (a < b)` into `b ≤ a` and `¬ (a ≤ b)` into `b < a` (R1–R5); `use` gives the
    witnesses and tries to close what is left (R6–R9).
H2. `not_all_small`: after `push Not` the goal is `∃ n, 5 ≤ n`. `exists_pair`: 7 = 3 + 4 and 12 = 3 * 4.
    `unbounded`: after `push Not` the goal is `∀ M, ∃ n, M < f n`; introduce `M`, then a witness built
    from `M` (`n := M` fails at `M = 0`).
H3. `push Not; use 5` · `use 3, 4` · `push Not; intro M; use M + 1; rw [hf]; omega`.
-/

/- E035 | linarith | 2 min | linarith, mathlib
GOAL
  Prove linear (in)equalities over ordered fields from hypotheses with `linarith`.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · solve_two
  1. `h1`, `h2` are linear equations in `x, y` and the goal is an equation;
     `linarith` reads both from the context. Close in one step:            R1
-/
-- BEGIN SPEC
theorem solve_two (x y : ℝ) (h1 : x + y = 10) (h2 : x - y = 2) : x = 6 :=
-- END SPEC
  sorry

/- SKELETON · chain_pos
  1. A chain of `<` and `≤` from `h1`, `h2`, `h3`, and a goal with a numeral
     coefficient; all linear. Close in one step:                           R2, R3
-/
-- BEGIN SPEC
theorem chain_pos (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : 0 < a) : 0 < 2 * c - a :=
-- END SPEC
  sorry

/- SKELETON · sq_bound
  1. Not linear, and no hypotheses: `linarith` alone fails. Compute
     `(x + y) ^ 2 - 4 * x * y` by hand and write it as a square `s ^ 2`;
     check the guess with `ring` if unsure:                                 W1
  2. The missing fact is `0 ≤ s ^ 2`, a proof term:                         R4
  3. Pass it to `linarith`, which expands the square into the monomials
     `x ^ 2`, `x * y`, `y ^ 2` and closes the goal:                         R5, R6
-/
-- BEGIN SPEC
theorem sq_bound (x y : ℝ) : 4 * x * y ≤ (x + y) ^ 2 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two are linear consequences of the hypotheses in the context; the third is not linear and
    has no hypotheses (R1–R3).
H2. `sq_bound` is linear in the monomials x², xy, y² once one more fact is known: `0 ≤ s ^ 2` for the
    square `s ^ 2 = (x + y) ^ 2 - 4 * x * y`, given as a hint to `linarith` (R4–R6).
H3. `linarith`, `linarith`, `linarith [sq_nonneg (x - y)]`.
-/

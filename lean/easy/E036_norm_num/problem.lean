/- E036 | norm_num | 1-2 min | norm_num, mathlib
GOAL
  Evaluate concrete numeric statements in ℝ, ℚ and ℤ with `norm_num`.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · pow_ten
  1. Only numerals, in `ℝ` (so `decide` cannot help): evaluate the power.        R1
-/
-- BEGIN SPEC
theorem pow_ten : (2 : ℝ) ^ 10 = 1024 :=
-- END SPEC
  sorry

/- SKELETON · frac_gt
  1. `(7 : ℚ)` makes `7 / 2` the fraction 7/2, not `ℕ` division (R5).
     Compare the two rationals.                                                  R2
-/
-- BEGIN SPEC
theorem frac_gt : (7 : ℚ) / 2 > 3 :=
-- END SPEC
  sorry

/- SKELETON · big_mod
  1. An integer remainder of numerals: evaluate it.                              R3
-/
-- BEGIN SPEC
theorem big_mod : (12345 : ℤ) % 7 = 4 :=
-- END SPEC
  sorry

/- SKELETON · inv_sum
  1. Inverses and a fraction of numerals in `ℝ`: evaluate both sides exactly.    R4
-/
-- BEGIN SPEC
theorem inv_sum : (3 : ℝ)⁻¹ + 6⁻¹ = 1 / 2 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. No variables appear: every statement is a closed numeric fact. In `ℝ`, `decide` and `rfl` cannot
    evaluate it (R1); you need a tactic that computes with exact numerals.
H2. `norm_num` evaluates `^`, `/`, `⁻¹` and `%` on literals and decides `=`, `<`, `>` between the results
    (R1–R4). The ascriptions `(… : ℝ)`, `(… : ℚ)`, `(… : ℤ)` fix what `/` and `%` mean (R5).
H3. Each proof is the single tactic `norm_num`.
-/

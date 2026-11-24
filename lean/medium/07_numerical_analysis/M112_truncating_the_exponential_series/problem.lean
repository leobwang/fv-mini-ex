/- M112 | Truncating the exponential series | 5-10 min | Real.exp_bound, Finset.sum_range_succ, norm_num, mathlib
GOAL
  Certify a numerical value: the truncated series `1 + 1/2 + (1/2)²/2 = 13/8` approximates `e^{1/2}`
  within `1/36`, using Mathlib's explicit remainder bound. Then derive the decimal bounds `1.59 < e^{1/2} < 1.66`.

BANNED: exp_one_gt_d9, exp_one_lt_d9, exp_one_near_10, exp_one_near_20, exp_half

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M112

/- SKELETON · exp_half_approx
  1. Add the remainder bound for x = 1/2 with three terms (n = 3):             R1, R2
       side goals: `|1 / 2| ≤ 1` by `norm_num` with R3;  `0 < 3` by `norm_num`
       (fix `n` by name BEFORE its side proof, or `norm_num` faces `0 < ?m`)
  2. Evaluate the sum and the constant in `h`, and normalise the goal alike:    R8
       the lemmas it needs: expand the sum R4 (R5 is automatic),
       factorials R6; `Nat.succ 3` and the casts go by themselves R7
     Now `h` reads `|Real.exp (1 / 2) - 13 / 8| ≤ 1 / 36`.
  3. Close:                                                                     R9
-/
-- BEGIN SPEC
theorem exp_half_approx : |Real.exp (1 / 2) - 13 / 8| ≤ 1 / 36 :=
-- END SPEC
  sorry

/- SKELETON · exp_half_bounds
  1. Open the absolute value of Part 1's theorem `exp_half_approx`:             R10
       h : -(1 / 36) ≤ Real.exp (1 / 2) - 13 / 8 ∧ Real.exp (1 / 2) - 13 / 8 ≤ 1 / 36
  2. Split the `∧` of the goal:                                                 constructor
  3. In both goals: decimals → fractions, then linear arithmetic with
     the two halves of `h`:                                                     R11, then R12 → R13
-/
-- BEGIN SPEC
theorem exp_half_bounds : 1.59 < Real.exp (1 / 2) ∧ Real.exp (1 / 2) < 1.66 :=
-- END SPEC
  sorry

end M112

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `13/8 = 1 + 1/2 + 1/8` is the sum of the first three terms of `∑ xᵐ/m!` at `x = 1/2`, and
    `Real.exp_bound` bounds the error of exactly that sum. Part 2 only needs Part 1 and arithmetic.
H2. Part 1: add the bound with `x = 1/2`, `n = 3` as a hypothesis, let `norm_num` expand the 3-term sum and
    the factorials in it and in the goal (the constant `(1/2)³ · 4/(3!·3)` becomes `1/36`), then `linarith`.
    Part 2: turn `exp_half_approx` into two inequalities with `abs_le`, split the goal, `linarith`.
H3. `have h := Real.exp_bound (x := 1 / 2) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)`, then
    `norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢`.
    Part 2: `have h := abs_le.mp exp_half_approx`; after the split, each side falls to `linarith [h.1, h.2]`.
-/

/- M072 | AM-GM for two reals | 10 min | nlinarith, sq_nonneg, Real.sqrt, mathlib
GOAL
  Prove the two-variable AM-GM inequality, in squared form and with a square root.

BANNED: Real.add_pow_le_pow_mul_pow_of_sq_le_sq, Real.inner_le_nnorm_mul_nnorm, Real.geom_mean_le_arith_mean2_weighted, Real.sqrt_mul_self_le, four_mul_le_sq_add
GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M072

/- SKELETON · two_mul_le
  1. Pick the square whose expansion is the gap  a ^ 2 + b ^ 2 - 2 * a * b:     R1
  2. Close with nlinarith, passing that square as the hint:                    R2
-/
-- BEGIN SPEC
theorem two_mul_le (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
-- END SPEC
  sorry

/- SKELETON · amgm_sq
  1. The gap  ((a + b) / 2) ^ 2 - a * b  is again a square divided by 4:        R1
  2. Close with nlinarith and that hint (same move as two_mul_le):             R2
-/
-- BEGIN SPEC
theorem amgm_sq (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 :=
-- END SPEC
  sorry

/- SKELETON · amgm
  1. Rewrite the right side as a root,  (a + b) / 2 = √(((a + b) / 2) ^ 2):    R3
       proof of that equation: R4 flipped by R5; R4's side goal
       0 ≤ (a + b) / 2  by R6 (it uses ha, hb)
  2. Now the goal compares two roots: monotonicity of √                        R7
       with the inequality between the arguments, which is amgm_sq a b (Part 2)
-/
-- BEGIN SPEC
theorem amgm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 :=
-- END SPEC
  sorry

end M072

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything follows from one square being nonnegative: `0 ≤ (a - b) ^ 2` (R1).
H2. The first two are polynomial inequalities: `nlinarith` closes them once it is given that square (R2).
    For the root version, write `(a + b) / 2` as `√(((a + b) / 2) ^ 2)` (valid since it is ≥ 0, R3–R6)
    and use that `√` is monotone (R7) with `amgm_sq`.
H3. `nlinarith [sq_nonneg (a - b)]` for both; then
    `rw [show (a + b) / 2 = Real.sqrt (((a + b) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]`
    and `exact Real.sqrt_le_sqrt (amgm_sq a b)`.
-/

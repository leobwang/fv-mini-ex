/- E108 | Floor and round | 2-3 min | Int.floor, round, casts, Int.floor_eq_iff, mathlib
GOAL
  Basic facts about rounding a real to an integer: `⌊x⌋` brackets `x`, rounding to the nearest integer
  errs by at most `1/2`, and three concrete values (floor of a negative, an ordinary round, a tie).

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E108

/- SKELETON · floor_bounds
  1. Split the `∧` into its two sides:                    constructor (or the term ⟨_, _⟩)
  2. Lower side `↑⌊x⌋ ≤ x`: one library lemma             R1
  3. Upper side `x < ↑⌊x⌋ + 1`: one library lemma         R2
-/
-- BEGIN SPEC
theorem floor_bounds (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < ⌊x⌋ + 1 :=
-- END SPEC
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

/- SKELETON · round_error
  1. The whole statement is one library lemma:            R3
-/
-- BEGIN SPEC
theorem round_error (x : ℝ) : |x - round x| ≤ 1 / 2 :=
-- END SPEC
  abs_sub_round x

/- SKELETON · rounding_examples
  1. Split the three equations:                           refine ⟨?_, ?_, ?_⟩
  2. On every goal (`<;>`):
       `round` → a floor (the first goal has none)        R4
       floor equation → two inequalities                  R5
       check the inequalities on decimals                 R6
     R7 does all three in one `norm_num` call. Use R7 after `<;>`: a bare
     `rw [round_eq]` fails on the first goal, which has no `round`.
-/
-- BEGIN SPEC
theorem rounding_examples :
    ⌊(-2.5 : ℝ)⌋ = -3 ∧ round (2.6 : ℝ) = 3 ∧ round (1 / 2 : ℝ) = 1 :=
-- END SPEC
  by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num [round_eq, Int.floor_eq_iff]

end E108

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two theorems are library facts about `⌊·⌋` and `round` (R1–R3); the third is arithmetic
    once `round` and `⌊·⌋` are turned into inequalities (R4, R5).
H2. `floor_bounds`: build the `∧` from `Int.floor_le` and `Int.lt_floor_add_one`. `round_error`:
    `abs_sub_round`. `rounding_examples`: split into three goals, then on each rewrite with `round_eq` and
    `Int.floor_eq_iff` and let `norm_num` compare the decimals.
H3. `⟨Int.floor_le x, Int.lt_floor_add_one x⟩`; `abs_sub_round x`;
    `refine ⟨?_, ?_, ?_⟩ <;> norm_num [round_eq, Int.floor_eq_iff]`.
-/

/- E108 | Floor and round | 2-3 min | Int.floor, round, casts, Int.floor_eq_iff, mathlib
GOAL
  Basic facts about rounding a real to an integer: `⌊x⌋` brackets `x`, rounding to the nearest integer
  errs by at most `1/2`, and three concrete values (floor of a negative, an ordinary round, a tie).

REFERENCE
  `⌊x⌋ : ℤ` (`Int.floor x`) is the largest integer `≤ x`; `round x : ℤ` is the nearest integer.
  `(⌊x⌋ : ℝ)` casts back to `ℝ`; Lean inserts the cast `↑` when an integer meets a real.
  #check Int.floor_le          -- (a : α) : ↑⌊a⌋ ≤ a
  #check Int.lt_floor_add_one  -- (a : R) : a < ↑⌊a⌋ + 1
  #check Int.floor_eq_iff      -- ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < ↑z + 1
  #check round_eq              -- round x = ⌊x + 1 / 2⌋
  #check abs_sub_round         -- |x - ↑(round x)| ≤ 1 / 2
  example : ⌊(3.7 : ℝ)⌋ = 3 := by norm_num [Int.floor_eq_iff]   -- decimals like 3.7 are exact rationals
NOTE: ⌊·⌋ rounds toward -∞; Mathlib's round sends ties up (round 0.5 = 1), unlike IEEE round-half-to-even.
-/
import Mathlib

namespace E108

-- BEGIN SPEC
theorem floor_bounds (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < ⌊x⌋ + 1 :=
-- END SPEC
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

-- BEGIN SPEC
theorem round_error (x : ℝ) : |x - round x| ≤ 1 / 2 :=
-- END SPEC
  abs_sub_round x

-- BEGIN SPEC
theorem rounding_examples :
    ⌊(-2.5 : ℝ)⌋ = -3 ∧ round (2.6 : ℝ) = 3 ∧ round (1 / 2 : ℝ) = 1 :=
-- END SPEC
  by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num [round_eq, Int.floor_eq_iff]

end E108

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first two are exactly library facts listed in the REFERENCE.
H2. Build the `∧` with `⟨_, _⟩`. For the concrete values, turn `round` into a floor with `round_eq`, and
    a floor equation into two inequalities with `Int.floor_eq_iff`.
H3. `rounding_examples`: `refine ⟨?_, ?_, ?_⟩ <;> norm_num [round_eq, Int.floor_eq_iff]`.
-/

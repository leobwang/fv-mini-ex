/- Guide for E108 (Floor and round).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on values that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E108Guide

/-! # Part R · Reference entries -/

/-! ## The two brackets and the rounding error (each lemma closes its goal)
`⌊a⌋` is `Int.floor a : ℤ`, the largest integer `≤ a`. `round a : ℤ` is the nearest integer.
`↑n` is the integer `n` cast back into the type of `a` (here `α`; in the exercise `ℝ`).
`[Ring α] [LinearOrder α] [FloorRing α]`: `α` has `+ - *`, a total order `≤`, and a floor function;
`ℝ` and `ℚ` qualify. -/

/-! ### R1. `Int.floor_le` · `↑⌊a⌋ ≤ a` · closes the goal -/
example {α : Type} [Ring α] [LinearOrder α] [FloorRing α] (a : α) : (⌊a⌋ : α) ≤ a := by
  exact Int.floor_le a

/-! ### R2. `Int.lt_floor_add_one` · `a < ↑⌊a⌋ + 1` · closes the goal -/
example {α : Type} [Ring α] [LinearOrder α] [FloorRing α] (a : α) : a < (⌊a⌋ : α) + 1 := by
  exact Int.lt_floor_add_one a

/-! ### R3. `abs_sub_round` · `|a - ↑(round a)| ≤ 1 / 2` · closes the goal
`|·|` is the absolute value. `round` needs division (for `1 / 2`): `[Field α]` instead of `[Ring α]`,
and `[IsStrictOrderedRing α]` says `+` and `*` respect `<`. `ℝ` and `ℚ` qualify. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] (a : α) :
    |a - (round a : α)| ≤ 1 / 2 := by
  exact abs_sub_round a

/-! ## Concrete values: from `round` to `⌊·⌋` to two inequalities -/

/-! ### R4. `round_eq` · `round a = ⌊a + 1 / 2⌋` · goal: `round` becomes a floor -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] (a : α)
    (P : ℤ → Prop) (h : P ⌊a + 1 / 2⌋) : P (round a) := by
  rw [round_eq]
  exact h

/-! ### R5. `Int.floor_eq_iff` · `⌊a⌋ = z ↔ ↑z ≤ a ∧ a < ↑z + 1` · goal: a floor equation becomes
the two inequalities that pin `z` down -/
example {α : Type} [Ring α] [LinearOrder α] [FloorRing α] (a : α) (z : ℤ)
    (h : (z : α) ≤ a ∧ a < z + 1) : ⌊a⌋ = z := by
  rw [Int.floor_eq_iff]
  exact h

/-! ### R6. `norm_num` · closes numeric goals with decimals and integer casts
A decimal such as `3.2 : ℝ` is the exact rational `32 / 10`, not a float. `norm_num` evaluates
`↑(-4)` to `-4` and compares the rationals. -/
example : ((-4 : ℤ) : ℝ) ≤ -3.2 ∧ (-3.2 : ℝ) < ((-4 : ℤ) : ℝ) + 1 := by
  norm_num

/-! ### R7. `norm_num [l₁, l₂]` · rewrites with the listed lemmas as it simplifies, then closes
Here `[round_eq, Int.floor_eq_iff]` is R4 then R5, then R6 on what is left. -/
example : round (0.7 : ℝ) = 1 := by
  norm_num [round_eq, Int.floor_eq_iff]

/-! # Part W · Worked combinations (not the exercise's values) -/

/-! ### W1. A floor of a negative decimal, step by step: R5, then R6.
`⌊·⌋` rounds toward −∞: `⌊-0.3⌋ = -1`, not `0`. -/
example : ⌊(-0.3 : ℝ)⌋ = -1 := by
  rw [Int.floor_eq_iff]
  norm_num

/-! ### W2. A round, step by step: R4, R5, R6 -/
example : round (3.2 : ℝ) = 3 := by
  rw [round_eq]
  rw [Int.floor_eq_iff]
  norm_num

/-! ### W3. Ties go up, also below zero: `round (-1/2) = ⌊0⌋ = 0`. R7 in one call -/
example : round (-1 / 2 : ℝ) = 0 := by
  norm_num [round_eq, Int.floor_eq_iff]

/-! ### W4. Two concrete values at once: split the `∧`, then R7 on every goal -/
example : ⌊(0.5 : ℝ)⌋ = 0 ∧ round (0.4 : ℝ) = 0 := by
  refine ⟨?_, ?_⟩ <;> norm_num [round_eq, Int.floor_eq_iff]

/-! ### W5. `simp` rewrites with R5 but cannot compare decimals; `norm_num` finishes -/
example : ⌊(3.7 : ℝ)⌋ = 3 := by
  simp [Int.floor_eq_iff]
  norm_num

end E108Guide

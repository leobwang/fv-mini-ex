/- Guide for E036 (norm_num).
Part R: one reference entry per use of `norm_num` the exercise needs, each on a statement of the same
kind as one hole but with other numbers. Put the cursor before and after the step to see the proof
state change in the infoview.
`P : ℝ → Prop` stands for "the rest of your goal": the step changes only the part shown inside
`P (…)`. A hypothesis `h` in an entry is only there to finish the example; it shows what the goal
became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E033 (tactic mode, `decide` from E001, `rw` from E009, `simp` from E010). New:
`import Mathlib`, the number types `ℤ ℚ ℝ`, type ascriptions `(n : T)` on numerals, and `norm_num`.
-/
import Mathlib

namespace E036Guide

/-! # Part R · Reference entries -/

/-! ## `norm_num` closes a goal built from numerals only -/

/-! ### R1. `norm_num` on `+ - * ^` of numerals in `ℝ` · closes the goal
`(3 : ℝ)` is the numeral `3` of type `ℝ`; the infoview prints it as plain `3`. `norm_num` evaluates
both sides exactly (no floating point) and compares them. -/
example : (3 : ℝ) ^ 4 - 1 = 80 := by
  norm_num

/-! ### R2. `norm_num` on an order between fractions in `ℚ` (`<`, `≤`, `>`, `≥`, `≠`) · closes the goal
`a > b` is notation for `b < a`. `norm_num` brings each side to a reduced fraction and compares. -/
example : (5 : ℚ) / 3 > 3 / 2 := by
  norm_num

/-! ### R3. `norm_num` on `%` and `/` in `ℤ` · closes the goal
`a % b` is the remainder and `a / b` the quotient of integer division. For `b > 0` the remainder
is always in `0 … b-1`, also for negative `a`: `-7 = 3 * (-3) + 2`. -/
example : (1000 : ℤ) % 9 = 1 := by
  norm_num

example : (-7 : ℤ) % 3 = 2 ∧ (-7 : ℤ) / 3 = -3 := by
  norm_num

/-! ### R4. `norm_num` on `⁻¹` and `/` in `ℝ` · closes the goal
`a⁻¹` is the inverse `1 / a`. `norm_num` computes with exact fractions, so `2⁻¹ + 4⁻¹` is `3 / 4`. -/
example : (2 : ℝ)⁻¹ + 4⁻¹ = 3 / 4 := by
  norm_num

/-! ## The type of a numeral decides what `/` and `-` mean -/

/-! ### R5. `(n : ℕ)` versus `(n : ℚ)` · `norm_num` closes the goal in either type, with different answers
One ascription fixes the type of the whole expression. Without any, a numeral defaults to `ℕ`, where
`/` rounds down and `-` stops at `0`. In `ℚ` (or `ℝ`), `7 / 2` is the fraction `7/2`, which is not `3`. -/
example : (7 : ℕ) / 2 = 3 ∧ (2 : ℕ) - 5 = 0 := by
  norm_num

example : (7 : ℚ) / 2 ≠ 3 := by
  norm_num

/-! ## `norm_num` when the goal is not purely numeric -/

/-! ### R6. `norm_num` that cannot close the goal · goal: the numeric parts evaluated, the rest left
Like `simp` (E010), it rewrites what it can and leaves the simplified goal. Unlike `simp`, it does
not fail when it changes nothing: the goal stays as it was and Lean warns "'norm_num' tactic does
nothing". -/
example (x : ℝ) (P : ℝ → Prop) (h : P (x + 6)) : P (x + 2 * 3) := by
  norm_num
  exact h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. `rw [h]` (E009), then R1: substitute a value, then evaluate -/
example (x : ℝ) (h : x = 3) : x ^ 2 + 1 = 10 := by
  rw [h]
  norm_num

/-! ### W2. R1 with `≠` in `ℝ`: `norm_num` proves that two numerals differ -/
example : (2 : ℝ) ^ 3 ≠ 9 := by
  norm_num

/-! ### W3. R2 and R4 together: an inverse inside a comparison in `ℚ` -/
example : (4 : ℚ)⁻¹ < 1 / 3 := by
  norm_num

end E036Guide

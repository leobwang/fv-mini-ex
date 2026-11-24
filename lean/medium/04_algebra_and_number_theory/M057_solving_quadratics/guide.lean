/- Guide for M057 (Solving x² = 4).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g`) in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is a goal the step does not touch.
Part W: worked combinations on equations that are NOT the exercise's (`y ² = 9`, `(y - 1)(y + 5) = 0`).
Assumed: Lean basics.
-/
import Mathlib

namespace M057Guide

/-! # Part R · Reference entries -/

/-! ## Proving the factored form -/

/-! ### R1. `ring_nf` · goal: every product multiplied out, like terms collected (ring normal form)
With symbols it gives the textbook form; with numerals it prints the constant first and the
coefficient after the variable (`6 - x * 5 + x ^ 2`). -/
example {α : Type} [CommRing α] (a b : α) (h : a ^ 2 - b ^ 2 = 0) : (a - b) * (a + b) = 0 := by
  ring_nf
  exact h

example (x : ℚ) (h : 4 - x * 5 + x ^ 2 = 0) : (x - 1) * (x - 4) = 0 := by
  ring_nf
  exact h

/-! ### R2. `linarith` · closes an equation or inequality that is a linear combination of hypotheses
Over an ordered field (`ℚ`, `ℝ`). A nonlinear term such as `x ^ 2` is treated as one unknown, so
`x ^ 2 = c` is a linear fact about the unknown `x ^ 2`. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (x c : α) (h : x ^ 2 = c) :
    -c + x ^ 2 = 0 := by
  linarith

example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (x c : α) (h : x - c = 0) :
    x = c := by
  linarith

/-! ## Splitting the product -/

/-! ### R3. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0` · context gains `a = 0 ∨ b = 0` (with `.mp`)
`.mp` is the left-to-right direction of the `↔`. -/
example {M₀ : Type} [MulZeroClass M₀] [NoZeroDivisors M₀] (a b : M₀) (hab : a * b = 0) (G : Prop)
    (g : a = 0 ∨ b = 0 → G) : G := by
  have h := mul_eq_zero.mp hab
  exact g h

/-! ### R4. `rcases h with h1 | h1` · goal list: one goal per side of `h : A ∨ B`
In the first goal the context has `h1 : A`, in the second `h1 : B`; `h` is gone.
`rcases mul_eq_zero.mp hab with h1 | h1` does R3 and R4 in one step. -/
example (A B G : Prop) (h : A ∨ B) (ga : A → G) (gb : B → G) : G := by
  rcases h with h1 | h1
  exact ga h1
  exact gb h1

/-! ## Choosing a side of the goal -/

/-! ### R5. `left` · goal: `A ∨ B` → `A` -/
example (A B : Prop) (ha : A) : A ∨ B := by
  left
  exact ha

/-! ### R6. `right` · goal: `A ∨ B` → `B` -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! # Part W · Worked combinations (not the exercise's equations) -/

/-! ### W1. A factored form from `y ^ 2 = 9`: R1 then R2 -/
example (y : ℚ) (h : y ^ 2 = 9) : (y - 3) * (y + 3) = 0 := by
  ring_nf
  linarith

/-! ### W2. From a product equal to zero to the two roots: R3 + R4, then R5/R6 and R2 in each goal -/
example (y : ℚ) (h : (y - 1) * (y + 5) = 0) : y = 1 ∨ y = -5 := by
  rcases mul_eq_zero.mp h with h1 | h1
  · left
    linarith
  · right
    linarith

end M057Guide

/- Guide for E067 (linear_combination).
Part R: one reference entry per tactic or coefficient form the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
A hypothesis `h` in an entry is one of the equations being combined.
Part W: worked combinations on systems that are NOT the exercise's.
Assumed: Lean basics (E001–E033).

How `linear_combination e` works. Every equation `l = r` stands for the expression `l - r`, which it
says is `0`. Proofs of equations can be combined like the expressions: if `h₁ : l₁ = r₁` and
`h₂ : l₂ = r₂`, then `c₁ * h₁ + c₂ * h₂` stands for `c₁ * l₁ + c₂ * l₂ = c₁ * r₁ + c₂ * r₂`.
For a goal `a = b` and a combination `e` standing for `l = r`, the tactic asks `ring` to prove
`(a - b) - (l - r) = 0`. Lean writes that goal as `a + r - (b + l) = 0` (R2).
-/
import Mathlib

namespace E067Guide

/-! # Part R · Reference entries -/

/-! ## The tactic -/

/-! ### R1. `linear_combination h` · goal list: `a = b` closed when `a - b` and `l - r` agree by `ring`
Here `a - (b - c)` and `(a + c) - b` are the same polynomial, so coefficient 1 works. -/
example {α : Type} [CommRing α] (a b c : α) (h : a + c = b) : a = b - c := by
  linear_combination h

/-! ### R2. `linear_combination (norm := skip) e` · goal: `a = b` → the identity `ring` would check
The option `(norm := skip)` stops before `ring`, so you see the goal `a + r - (b + l) = 0`; finish it
with `ring`. Use it to debug a coefficient choice; drop it in the final proof. -/
example {α : Type} [CommRing α] (a b c : α) (h : a + c = b) : a = b - c := by
  linear_combination (norm := skip) h
  ring

/-! ## Coefficient forms -/

/-! ### R3. `h₁ + h₂` · goal: the identity now has `(l₁ + l₂) - (r₁ + r₂)` in place of `l - r`
Adding two equations gives `l₁ + l₂ = r₁ + r₂`; `h₁ - h₂` subtracts them. -/
example {α : Type} [CommRing α] (a b c d : α) (h₁ : a + b = c) (h₂ : a - b = d) :
    2 * a = c + d := by
  linear_combination (norm := skip) h₁ + h₂
  ring

/-! ### R4. `e / 2` · goal: the identity now has `l / 2 - r / 2` in place of `l - r`
Dividing an equation by a numeral gives `l / 2 = r / 2`. Needs division (`Field α`) and `2 ≠ 0` (`CharZero α`); `ℝ` and `ℂ` have both. -/
example {α : Type} [Field α] [CharZero α] (a c : α) (h : 2 * a = c) : a = c / 2 := by
  linear_combination (norm := skip) h / 2
  ring

/-! ### R5. `t * h` with a term `t` · goal: the identity now has `t * l - t * r` in place of `l - r`
Multiplying an equation by an expression gives `t * l = t * r`. Here `a ^ 2 - b ^ 2 = (a + b) * (a - b)`: factor the goal's difference to find `t`. -/
example {α : Type} [CommRing α] (a b : α) (h : a = b) : a ^ 2 = b ^ 2 := by
  linear_combination (norm := skip) (a + b) * h
  ring

/-! ### R6. `h₁ - t * h₂` · goal: the identity subtracts a multiple of a second equation
`h₁` alone leaves `d * b - a * b`; `b * h₂` stands for `b * a - b * d` and cancels it. -/
example {α : Type} [CommRing α] (a b c d : α) (h₁ : a * b = c) (h₂ : a = d) : d * b = c := by
  linear_combination (norm := skip) h₁ - b * h₂
  ring

/-! # Part W · Worked combinations (not the exercise's systems) -/

/-! ### W1. A linear system over `ℝ`: add the equations (R3), then divide (R4)
`(2x + y - 7) + (x - y + 1) = 3x - 6 = 3 (x - 2)`. -/
example (x y : ℝ) (h₁ : 2 * x + y = 7) (h₂ : x - y = -1) : x = 2 := by
  linear_combination (norm := skip) (h₁ + h₂) / 3
  ring

/-! ### W2. A quadratic identity: a term coefficient (R5) plus a numeral multiple
`a² + b² - 13 = (a - b)² - 1 + 2 (a b - 6)` and `(a - b)² - 1 = (a - b + 1) (a - b - 1)`. -/
example (a b : ℝ) (h : a - b = 1) (h₂ : a * b = 6) : a ^ 2 + b ^ 2 = 13 := by
  linear_combination (a - b + 1) * h + 2 * h₂

/-! ### W3. Over `ℂ`, which has no `≤`: divide (R4), then cancel with a term multiple (R6)
`(z w - 3) / 3 = z w / 3 - 1` leaves `z - z w / 3 = -(z / 3) (w - 3)`. -/
example (z w : ℂ) (h₁ : z * w = 3) (h₂ : w = 3) : z = 1 := by
  linear_combination h₁ / 3 - z / 3 * h₂

end E067Guide

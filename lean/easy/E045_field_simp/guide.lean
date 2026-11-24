/- Guide for E045 (field_simp).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`{α : Type}` is any type; a bracket such as `[Field α]` says what `α` must support (a type class).
`P : Prop` (or `P : α → Prop`) stands for "the rest of your goal". A hypothesis `hP` in an entry is
only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E033 (tactic mode, `have`, `Iff.mpr`), E034 (`ring`), E035 (`linarith`).
New: the type class `Field`, Lean's convention `a / 0 = 0`, the tactic `field_simp`, `sub_ne_zero`.
-/
import Mathlib

namespace E045Guide

/-! # Part R · Reference entries -/

/-! ## Clearing a denominator in the goal -/

/-! ### R1. `field_simp` · closes the goal (it cancels `b` against `b`, given `b ≠ 0`)
`[Field α]`: `α` has `0 1 + - * /`, `*` is commutative, and every `b ≠ 0` has an inverse; `ℚ`, `ℝ`,
`ℂ` qualify. Lean defines `a / 0 = 0`, so `a * b / b = a` is false at `b = 0`: `field_simp` cancels
`b` only when it finds `hb : b ≠ 0` (or can derive it) from the context. -/
example {α : Type} [Field α] (a b : α) (hb : b ≠ 0) : a * b / b = a := by
  field_simp

/-! ### R2. `have h : a - b ≠ 0 := sub_ne_zero.mpr hab` · context gains `h : a - b ≠ 0`
`sub_ne_zero : a - b ≠ 0 ↔ a ≠ b` (for `[AddGroup α]`: `+ -` with `0`; every field qualifies).
`.mpr` is the right-to-left direction, `a ≠ b → a - b ≠ 0`. This is the form `field_simp` wants for
a denominator `a - b`. -/
example {α : Type} [AddGroup α] (a b : α) (hab : a ≠ b) (P : Prop) (hP : a - b ≠ 0 → P) : P := by
  have h : a - b ≠ 0 := sub_ne_zero.mpr hab
  exact hP h

/-! ### R3. `field_simp` · goal: `a / b = c` → `a = b * c` (multiply both sides by `b`)
When the cancellation does not close the goal, `field_simp` leaves an equation with no `/` left in
it. It chooses the order of factors itself (`b * c`, not `c * b`). -/
example {α : Type} [Field α] (a b c : α) (hb : b ≠ 0) (hP : a = b * c) : a / b = c := by
  field_simp
  exact hP

/-! ### R4. `ring` · closes an identity of commutative rings (E034)
After R3 the goal is usually a polynomial identity; `ring` finishes it. -/
example {α : Type} [Field α] (a b : α) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

/-! ## Clearing a denominator in a hypothesis -/

/-! ### R5. `field_simp at h` · context: `h : a / b = c` → `h : a = b * c`; goal unchanged -/
example {α : Type} [Field α] (a b c : α) (hb : b ≠ 0) (h : a / b = c) (P : α → Prop)
    (hP : a = b * c → P a) : P a := by
  field_simp at h
  exact hP h

/-! ### R6. `linarith` · closes a goal that follows linearly from the hypotheses (E035)
`b * 5` counts as linear: a numeral times a variable, in either order. `exact h` would fail here,
because `b * 5` and `5 * b` are different terms. -/
example (a b : ℝ) (h : a = b * 5) : a = 5 * b := by
  linarith

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R2, then R1: a denominator `b - c` with only `b ≠ c` known -/
example {α : Type} [Field α] (a b c : α) (hbc : b ≠ c) : a / (b - c) * (b - c) = a := by
  have h : b - c ≠ 0 := sub_ne_zero.mpr hbc
  field_simp

/-! ### W2. R3, then R4: adding fractions -/
example {α : Type} [Field α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp
  ring

/-! ### W3. R5, then R6: a ratio in a hypothesis -/
example (a b : ℝ) (hb : b ≠ 0) (h : (a + 1) / b = 2) : a = 2 * b - 1 := by
  field_simp at h
  linarith

end E045Guide

/- Guide for E069 (Junk values).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`√(-9)`, `x * x⁻¹`, `ℕ` and `ℤ`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E069Guide

/-! # Part R · Reference entries -/

/-! ## Junk values: total versions of partial operations -/

/-! ### R1. `div_zero` · `a / 0 = 0` · goal: `a / 0` → `0`
As a proof term, `div_zero a : a / 0 = 0`. -/
example {α : Type} [GroupWithZero α] (a : α) (P : α → Prop) (h : P 0) : P (a / 0) := by
  rw [div_zero]
  exact h

/-! ### R2. `Real.sqrt_eq_zero_of_nonpos` · `x ≤ 0 → √x = 0` · `apply`: goal `√x = 0` → `x ≤ 0`
`√x` is how Lean prints `Real.sqrt x`. -/
example (x : ℝ) (hx : x ≤ 0) : Real.sqrt x = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  exact hx

/-! ### R3. `linarith` · closes a linear (in)equality over `ℝ` from the hypotheses and numerals -/
example (a : ℝ) (ha : 0 ≤ a) : -a ≤ 0 := by
  linarith

/-! ### R4. `Real.log_zero` · `Real.log 0 = 0` · goal: `Real.log 0` → `0` -/
example (P : ℝ → Prop) (h : P 0) : P (Real.log 0) := by
  rw [Real.log_zero]
  exact h

/-! ## The honest lemma carries a side condition -/

/-! ### R5. `div_self` · `a ≠ 0 → a / a = 1` · goal rewritten, plus side goal `a ≠ 0`
As a proof term, `div_self ha : a / a = 1` for `ha : a ≠ 0`. -/
example {α : Type} [GroupWithZero α] (a : α) (ha : a ≠ 0) (P : α → Prop) (h : P 1) :
    P (a / a) := by
  rw [div_self]
  exact h
  exact ha

/-! ## Refuting a `∀` -/

/-! ### R6. `intro h` on `¬A` · `¬A` is `A → False`: context gains `h : A`, goal → `False` -/
example (A : Prop) (k : A → False) : ¬A := by
  intro h
  exact k h

/-! ### R7. `have h0 := h a` · context gains `h0 : P a`, the `∀` hypothesis used at `a` -/
example {α : Type} (P : α → Prop) (a : α) (h : ∀ x, P x) : P a := by
  have h0 := h a
  exact h0

/-! ### R8. `rw [lemma] at h0` · context: rewrites the hypothesis `h0`, goal unchanged -/
example {α : Type} [GroupWithZero α] (a : α) (Q : α → Prop) (h0 : Q (a / 0)) : Q 0 := by
  rw [div_zero] at h0
  exact h0

/-! ### R9. `zero_ne_one` · `(0 : α) ≠ 1`; a `≠` applied to an equality is `False`
`b ≠ c` is `b = c → False`, so `zero_ne_one h0 : False` for `h0 : 0 = 1`. -/
example {α : Type} [Zero α] [One α] [NeZero (1 : α)] (h0 : (0 : α) = 1) : False := by
  exact zero_ne_one h0

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A square root of a negative numeral: R2, then R3 on the side goal -/
example : Real.sqrt (-9) = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  linarith

/-! ### W2. `x * x⁻¹ = 1` also fails at `0`: R6, R7, R8 twice, R9
`inv_zero : 0⁻¹ = 0` and `mul_zero : a * 0 = 0`. -/
example : ¬ ∀ x : ℝ, x * x⁻¹ = 1 := by
  intro h
  have h0 := h 0
  rw [inv_zero] at h0
  rw [mul_zero] at h0
  exact zero_ne_one h0

/-! ### W3. `ℕ` and `ℤ` divide by zero to `0` too (`Nat.div_zero`, `Int.ediv_zero`), as proof terms -/
example (n : ℕ) (m : ℤ) : n / 0 = 0 ∧ m / 0 = 0 :=
  ⟨Nat.div_zero n, Int.ediv_zero m⟩

end E069Guide

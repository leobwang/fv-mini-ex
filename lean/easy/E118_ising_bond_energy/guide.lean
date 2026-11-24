/- Guide for E118 (Ising bond energy).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a spin of size 2, a product of
two spins).
Assumed: Lean basics (E001–E033): `cases`, `<;>`, `simp [defs]`, `exact`.
-/
import Mathlib

namespace E118Guide

/-! # Part R · Reference entries -/

/-! ## Splitting on `Bool` -/

/-! ### R1. `cases b` (`b : Bool`) · goal list: one goal per value, `false` first
The context loses `b`; in each goal `b` is replaced by the literal `false` or `true`. -/
example (P : Bool → Prop) (h0 : P false) (h1 : P true) (b : Bool) : P b := by
  cases b
  exacts [h0, h1]

/-! ### R2. `cases a <;> cases b` · goal list: four goals, one per pair of values
`<;>` runs `cases b` in both goals `cases a` made. Goals are named `false.false`, `false.true`, … -/
example (P : Bool → Bool → Prop) (h00 : P false false) (h01 : P false true) (h10 : P true false)
    (h11 : P true true) (a b : Bool) : P a b := by
  cases a <;> cases b
  exacts [h00, h01, h10, h11]

/-! ## What `simp [defs]` does, one rewrite at a time -/

/-! ### R3. `simp only [D]` · goal: the name `D` → its body
For a `Bool` condition, `if b then x else y` is stored as `if b = true then x else y`. -/
def D (b : Bool) : ℝ := if b then 2 else 0
example (P : ℝ → Prop) (b : Bool) (h : P (if b = true then 2 else 0)) : P (D b) := by
  simp only [D]
  exact h

/-! ### R4. `Bool.not_true`, `Bool.not_false` · `(!true) = false`, `(!false) = true` · goal -/
example (P : Bool → Prop) (h : P false) : P (!true) := by
  rw [Bool.not_true]
  exact h

example (P : Bool → Prop) (h : P true) : P (!false) := by
  rw [Bool.not_false]
  exact h

/-! ### R5. `Bool.false_eq_true` · `(false = true) = False` · goal: the condition becomes `False`
`true = true` needs no lemma: `simp` turns it into `True` by itself (it is `rfl`). -/
example (P : Prop → Prop) (h : P False) : P (false = true) := by
  rw [Bool.false_eq_true]
  exact h

/-! ### R6. `↓reduceIte` · goal: `if True then x else y` → `x`, `if False then x else y` → `y`
A *simproc* (a procedure `simp` runs, not a lemma). `↓` means it runs before `simp` looks inside the
branches. The lemma versions are `if_pos : c → (if c then x else y) = x` and `if_neg`. -/
example {α : Type} (x y : α) (P : α → Prop) (h : P x) : P (if True then x else y) := by
  simp only [↓reduceIte]
  exact h

example {α : Type} (x y : α) (P : α → Prop) (h : P y) : P (if False then x else y) := by
  simp only [↓reduceIte]
  exact h

/-! ## Arithmetic with `±1` -/

/-! ### R7. `mul_one` · `a * 1 = a` · goal -/
example {α : Type} [MulOneClass α] (a : α) (P : α → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R8. `mul_neg` · `a * -b = -(a * b)` · goal: a minus sign moves out of the right factor -/
example {α : Type} [Mul α] [HasDistribNeg α] (a b : α) (P : α → Prop) (h : P (-(a * b))) :
    P (a * -b) := by
  rw [mul_neg]
  exact h

/-! ### R9. `neg_neg` · `- -a = a` · goal -/
example {α : Type} [InvolutiveNeg α] (a : α) (P : α → Prop) (h : P a) : P (- -a) := by
  rw [neg_neg]
  exact h

/-! ## Closing the conjunction -/

/-! ### R10. `and_self` · `(A ∧ A) = A` · goal
`simp` first turns each `x = x` into `True` (`rfl`), then `True ∧ True` into `True` with this lemma. -/
example (A : Prop) (h : A) : A ∧ A := by
  rw [and_self]
  exact h

example {α : Type} (x y : α) : x = x ∧ y = y := by simp only [and_self]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R1, then R3, then R4–R6, then R9, on a spin of size 2
`simp only [mag]` already turns `true = true` into `True`; `(!false) = true` still needs R4.
The `true` goal closes at the third step (`-2 = -2` is `rfl`). -/
def mag (b : Bool) : ℝ := if b then 2 else -2

example (a : Bool) : mag (!a) = -mag a := by
  cases a
  all_goals simp only [mag]
  all_goals simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [neg_neg]

/-! The same in one line: `simp [mag]` applies R3–R9 by itself. -/
example (a : Bool) : mag (!a) = -mag a := by
  cases a <;> simp [mag]

/-! ### W2. R2, then `simp` with two definitions: flipping one spin negates a product -/
def link (a b : Bool) : ℝ := mag a * mag b

example (a b : Bool) : link (!a) b = -link a b := by
  cases a <;> cases b <;> simp [link, mag]

/-! ### W3. The `±1` arithmetic as a chain: R8, R7, R9, R7 -/
example (t : ℝ) : t * (-1 * -1) = t := by
  rw [mul_neg]
  rw [mul_one]
  rw [neg_neg]
  rw [mul_one]

end E118Guide

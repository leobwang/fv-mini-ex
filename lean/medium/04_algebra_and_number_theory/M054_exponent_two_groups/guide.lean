/- Guide for M054 (Exponent-2 groups are abelian).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on a group where every element CUBES to `1` (not the exercise's).
Assumed: Lean basics.
-/
import Mathlib

namespace M054Guide

/-! # Part R · Reference entries -/

/-! ## Inverses from an equation -/

/-! ### R1. `apply inv_eq_of_mul_eq_one_right` · goal `a⁻¹ = b` → goal `a * b = 1`
Lemma: `inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b` (`a b` implicit, read off the goal). -/
example {G : Type} [Group G] (a b : G) (h : a * b = 1) : a⁻¹ = b := by
  apply inv_eq_of_mul_eq_one_right
  exact h

/-! ### R2. `exact h x` · a `∀` hypothesis applied to one element closes the goal
`h : ∀ g, P g` is a function: `h x : P x`. A proved theorem is used the same way, one argument
per binder: `T h₀ x`. -/
example {G : Type} (P : G → Prop) (h : ∀ g : G, P g) (x : G) : P x := by
  exact h x

/-! ## Chains of equations -/

/-! ### R3. `calc` · goal `a = d` → one goal per step written `?_`
Each step `_ = c := proof` continues from the right side of the previous one. -/
example {α : Type} (a b c d : α) (hab : a = b) (hbc : b = c) (hcd : c = d) : a = d := by
  calc a = b := hab
    _ = c := ?_
    _ = d := hcd
  exact hbc

/-! ### R4. `Eq.symm` (`h.symm`) · goal `b = a` → goal `a = b`
As a term: from `h : a = b`, `h.symm : b = a`. -/
example {α : Type} (a b : α) (h : a = b) : b = a := by
  apply Eq.symm
  exact h

/-! ### R5. `mul_inv_rev` · `(a * b)⁻¹ = b⁻¹ * a⁻¹` · goal: inverse of a product, order reversed -/
example {G : Type} [Group G] (a b : G) (P : G → Prop) (h : P (b⁻¹ * a⁻¹)) : P (a * b)⁻¹ := by
  rw [mul_inv_rev]
  exact h

/-! ### R6. `rw [hinv]` with `hinv : ∀ g, g⁻¹ = g` · goal: ONE inverse removed per `rw`
`rw` fixes `g` at the first match (`b⁻¹` here) and rewrites only copies of that instance. -/
example {G : Type} [Group G] (a b : G) (hinv : ∀ g : G, g⁻¹ = g) (P : G → Prop) (h : P (b * a)) :
    P (b⁻¹ * a⁻¹) := by
  rw [hinv]
  rw [hinv]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects)
Here every element cubes to `1`: `h3 : ∀ g : G, g * g * g = 1`. One more lemma appears:
`mul_assoc : a * b * c = a * (b * c)` (`*` groups to the left, so `a * b * c` is `(a * b) * c`). -/

/-! ### W1. An inverse from a power law: R1, then `rw [← mul_assoc]`, then R2 -/
theorem inv_eq_sq {G : Type} [Group G] (h3 : ∀ g : G, g * g * g = 1) (a : G) :
    a⁻¹ = a * a := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc]
  exact h3 a

/-! ### W2. A calc chain that uses W1 as a function (R2), reversed (R4), then R5 and R6 -/
example {G : Type} [Group G] (h3 : ∀ g : G, g * g * g = 1) (a b : G) :
    a * b * (a * b) = b * b * (a * a) :=
  calc a * b * (a * b) = (a * b)⁻¹ := (inv_eq_sq h3 (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * b * (a * a) := by rw [inv_eq_sq h3, inv_eq_sq h3]

end M054Guide

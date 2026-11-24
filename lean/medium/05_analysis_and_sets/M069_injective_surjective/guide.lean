/- Guide for M069 (Injective and surjective).
Part R: one reference entry per tactic, definition or library lemma the exercise needs, stated with
typed placeholders. Put the cursor before and after the step to see the proof state change in the
infoview. `P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on concrete functions of ℕ and ℤ (NOT the exercise's statements).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Function

namespace M069Guide

/-! # Part R · Reference entries -/

/-! ## Injective -/

/-! ### R1. `Function.Injective` (see it with `unfold`) · goal: the name → its `∀` statement
`⦃a₁ a₂⦄` are strict-implicit binders: `hf h` fills `a₁ a₂` from `h : f a₁ = f a₂`. -/
example {α β : Type} (f : α → β) (h : ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂) : Injective f := by
  unfold Function.Injective
  exact fun a₁ a₂ e => h a₁ a₂ e

/-! ### R2. `intro a b h` on `Injective f` · context gains `a b : α`, `h : f a = f b`; goal `a = b`
`intro` unfolds `Injective` by itself; R1 is never needed in a proof. -/
example {α β : Type} (f : α → β) (k : ∀ a b : α, f a = f b → a = b) : Injective f := by
  intro a b h
  exact k a b h

/-! ### R3. `apply hf` with `hf : Injective f` · goal `a = b` → `f a = f b`
The term form is `hf h : a = b` for `h : f a = f b`. -/
example {α β : Type} (f : α → β) (hf : Injective f) (a b : α) (h : f a = f b) : a = b := by
  apply hf
  exact h

/-! ## Composition -/

/-! ### R4. `Function.comp_apply` · `(f ∘ g) x = f (g x)` · goal: an applied composite → nested calls
It holds by definition (`rfl`), so `exact`, `apply` and `rfl` see through `∘` without it. -/
example {α β γ : Type} (f : β → γ) (g : α → β) (x : α) (P : γ → Prop) (h : P (f (g x))) :
    P ((f ∘ g) x) := by
  rw [Function.comp_apply]
  exact h

/-! ## Surjective -/

/-! ### R5. `Function.Surjective` (see it with `unfold`) · goal: the name → its `∀ ∃` statement -/
example {α β : Type} (f : α → β) (h : ∀ b : β, ∃ a, f a = b) : Surjective f := by
  unfold Function.Surjective
  exact h

/-! ### R6. `intro c` on `Surjective f` · context gains `c : β`; goal `∃ a, f a = c` -/
example {α β : Type} (f : α → β) (k : ∀ c : β, ∃ a, f a = c) : Surjective f := by
  intro c
  exact k c

/-! ### R7. `obtain ⟨a, ha⟩ := hf c` · context gains a witness `a` and `ha : f a = c`
`hf c : ∃ a, f a = c`; `obtain` takes the `∃` apart. -/
example {α β : Type} (f : α → β) (hf : Surjective f) (c : β) (P : β → Prop)
    (k : ∀ a, P (f a)) : P c := by
  obtain ⟨a, ha⟩ := hf c
  rw [← ha]
  exact k a

/-! ### R8. `obtain ⟨a, rfl⟩ := hf c` · context loses `c`; every `c` becomes `f a`
Works only when `c` is a local variable (`intro`duced, not a fixed expression). -/
example {α β : Type} (f : α → β) (hf : Surjective f) (c : β) (P : β → Prop)
    (k : ∀ a, P (f a)) : P c := by
  obtain ⟨a, rfl⟩ := hf c
  exact k a

/-! ### R9. `refine ⟨x, ?_⟩` · goal `∃ a, f a = y` → `f x = y`
In one step: `exact ⟨x, hx⟩`; when `f x` and `y` agree by definition, `exact ⟨x, rfl⟩`. -/
example {α β : Type} (f : α → β) (x : α) (y : β) (hx : f x = y) : ∃ a, f a = y := by
  refine ⟨x, ?_⟩
  exact hx

/-! ### R10. `simp [h]` with `h : g x = g y` · closes `(f ∘ g) x = (f ∘ g) y`
`simp` unfolds `∘` (R4) by itself, rewrites `g x` to `g y` with `h`, then both sides are equal. -/
example {α β γ : Type} (f : β → γ) (g : α → β) (x y : α) (h : g x = g y) :
    (f ∘ g) x = (f ∘ g) y := by
  simp [h]

/-! # Part W · Worked combinations (concrete functions, not the exercise's) -/

/-! ### W1. Injectivity of a concrete function: R2, then `h` still shows the `fun`; `simp at h` -/
example : Injective (fun n : ℕ => 2 * n + 1) := by
  intro a b h
  simp at h
  exact h

/-! ### W2. Surjectivity of a concrete function: R6, then R9 with an explicit witness -/
example : Surjective (fun n : ℤ => n + 1) := by
  intro c
  refine ⟨c - 1, ?_⟩
  simp

/-! ### W3. R6, R7 (on `c - 1`, not `c`, so `rfl` cannot be used), R9, R10 -/
example (f : ℕ → ℤ) (hf : Surjective f) : Surjective (fun n => f n + 1) := by
  intro c
  obtain ⟨a, ha⟩ := hf (c - 1)
  refine ⟨a, ?_⟩
  simp [ha]

/-! ### W4. R3 in term form: `hf h` turns an equation of outputs into one of inputs -/
example (f : ℕ → ℕ) (hf : Injective f) (a b : ℕ) (h : f (a + 1) = f (b + 1)) : a = b := by
  have e : a + 1 = b + 1 := hf h
  omega

end M069Guide

/- Guide for E081 (Quotients).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries that need a concrete relation use `mod3` below (ℕ modulo "same remainder mod 3"), NOT
the exercise's relation.
Part W: worked combinations on `Tri` (the classes of `mod3`), not on the exercise's `Parity`.
Assumed: Lean basics (E001–E033), in particular `↔` and anonymous constructors (E005), `fun`
binders, `refine … ?_` (E031), `unfold` (E030), `rfl` and `simp [h]`.
-/

namespace E081Guide

/-- `a` and `b` are related when they leave the same remainder mod 3. A `Setoid α` bundles a
relation `r : α → α → Prop` with a proof `iseqv` that it is an equivalence relation. -/
def mod3 : Setoid Nat where
  r a b := a % 3 = b % 3
  iseqv := { refl := fun _ => rfl, symm := Eq.symm, trans := Eq.trans }

/-- The type of classes of `mod3`: three elements, the classes of `0`, `1`, `2`. -/
def Tri : Type := Quotient mod3

/-- The class of `n`. -/
def Tri.mk (n : Nat) : Tri := Quotient.mk mod3 n

/-! # Part R · Reference entries -/

/-! ## A function out of a quotient -/

/-! ### R1. `Quotient.lift f ?_` · goal: a function `Quotient s → β` → the obligation that `f` respects `≈`
`Quotient.lift : (f : α → β) → (∀ a b, a ≈ b → f a = f b) → Quotient s → β`. -/
example {α β : Type} {s : Setoid α} (f : α → β) (hf : ∀ a b, a ≈ b → f a = f b) :
    Quotient s → β := by
  refine Quotient.lift f ?_
  exact hf

/-! ### R2. `refine fun a b (h : a % 3 = b % 3) => ?_` · context gains `a b` and `h`, stated as the relation
`a ≈ b` unfolds (by definition) to `mod3.r a b`, which is `a % 3 = b % 3`; the type ascription
`(h : …)` makes Lean display and use `h` in that form. Plain `intro a b h` gives `h : a ≈ b`. -/
example (f : Nat → Bool) (hf : ∀ a b, a % 3 = b % 3 → f a = f b) : Quotient mod3 → Bool := by
  refine Quotient.lift f ?_
  refine fun a b (h : a % 3 = b % 3) => ?_
  exact hf a b h

/-! ### R3. `simp [h]` with `h : u = v` · closes `g u = g v` (rewrites `u` to `v`, then both sides agree) -/
example {α β : Type} (g : α → β) (u v : α) (h : u = v) : g u = g v := by
  simp [h]

/-! ## Computing on a class -/

/-! ### R4. `Quotient.lift f hf (Quotient.mk s a)` is `f a` by definition · goal: `show` the computed form
Core Lean has no rewrite lemma for it; `show` and `rfl` see through it. -/
example {α β : Type} {s : Setoid α} (f : α → β) (hf : ∀ a b, a ≈ b → f a = f b) (a : α)
    (P : β → Prop) (h : P (f a)) : P (Quotient.lift f hf (Quotient.mk s a)) := by
  show P (f a)
  exact h

/-! ### R5. `unfold Tri.mk` · goal: a wrapper definition → its body
`rfl` unfolds such definitions by itself; `unfold` only shows the step. -/
example (n : Nat) (P : Tri → Prop) (h : P (Quotient.mk mod3 n)) : P (Tri.mk n) := by
  unfold Tri.mk
  exact h

/-! ## Equal classes ↔ related representatives -/

/-! ### R6. `Quotient.sound` · `a ≈ b → Quotient.mk s a = Quotient.mk s b` · goal: equal classes → `a ≈ b` -/
example {α : Type} {s : Setoid α} (a b : α) (h : a ≈ b) : Quotient.mk s a = Quotient.mk s b := by
  apply Quotient.sound
  exact h

/-! ### R7. `show 4 % 3 = 7 % 3` · goal: `4 ≈ 7` → the relation it unfolds to; then `rfl` computes it
`rfl` alone also proves `4 ≈ 7`: Lean unfolds `≈` and evaluates both remainders to `1`. -/
example : Tri.mk 4 = Tri.mk 7 := by
  apply Quotient.sound
  show 4 % 3 = 7 % 3
  rfl

/-! ### R8. `refine ⟨fun h => ?_, fun h => ?_⟩` · goal `A ↔ B` → two goals, each with its hypothesis `h` -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  exact hab h
  exact hba h

/-! ### R9. `Quotient.exact` · `Quotient.mk s a = Quotient.mk s b → a ≈ b` · context gains `h' : a ≈ b` -/
example {α : Type} {s : Setoid α} (a b : α) (G : Prop) (g : a ≈ b → G)
    (h : Quotient.mk s a = Quotient.mk s b) : G := by
  have h' := Quotient.exact h
  exact g h'

/-! # Part W · Worked combinations (on `Tri`, not the exercise's `Parity`) -/

/-! ### W1. A lift whose obligation is the hypothesis itself: R1, R2 in term mode
The remainder mod 3 respects `mod3` by the very definition of `mod3`. -/
def Tri.rem : Tri → Nat := Quotient.lift (fun n => n % 3) (fun _ _ (h : _ % 3 = _ % 3) => h)

/-! ### W2. Computing a lifted function on a class: R5, R4, then `rfl` (or `rfl` alone) -/
example (n : Nat) : Tri.rem (Tri.mk n) = n % 3 := by
  unfold Tri.mk
  show n % 3 = n % 3
  rfl

/-! ### W3. Equal classes from a computation, as a term: R6 applied to `rfl` (R7) -/
example : Tri.mk 2 = Tri.mk 11 := Quotient.sound rfl

/-! ### W4. One direction of "equal classes": R9 as a term. `h` names the equation first, so Lean can
see through `Tri.mk` and find the setoid. -/
example (a b : Nat) : Tri.mk a = Tri.mk b → a % 3 = b % 3 := fun h => Quotient.exact h

end E081Guide

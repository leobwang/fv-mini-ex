/- Guide for H003 (Diaconescu: choice implies excluded middle).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a function `pick` that takes a
proof argument, predicates on `Nat`, a function `f : Nat → Bool`).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean, and nothing here uses
`Classical.choice` (check any example with `#print axioms`).
-/

namespace H003Guide

/-! # Part R · Reference entries -/

/-! ## Equal arguments give equal results, even when an argument is a proof -/

/-! ### R1. `subst h` · context: a local variable is replaced everywhere, hypothesis types included
`h : P = Q` with `Q` a local variable: `subst h` deletes `Q` and `h` and writes `P` for `Q` in the goal
and in every hypothesis (here in the type of `hQ`). `rw [h]` only rewrites the goal, and fails when
another term's type depends on the rewritten part ("motive is not type correct"). -/
example {α : Type} (P Q : α → Prop) (a : α) (h : P = Q) (hQ : Q a) : P a := by
  subst h
  exact hQ

/-! ### R2. `rfl` on proof arguments (proof irrelevance) · closes `f h₁ = f h₂` for `h₁ h₂ : A`
Any two proofs of the same proposition `A : Prop` are definitionally equal in Lean, so a function
applied to two different proofs gives definitionally equal results. No axiom is used. -/
example {A : Prop} {β : Type} (f : A → β) (h₁ h₂ : A) : f h₁ = f h₂ := by
  rfl

/-! ## Proving an equation between predicates -/

/-! ### R3. `apply hc` · goal: the conclusion of `hc` is matched; its premise becomes the goal
`hc` is a hypothesis or lemma `∀ a b, a = b → f a = f b`; `apply` finds `a`, `b` from the goal. When
`hc` also takes arguments the goal cannot reveal, pass them: `apply hc x`. -/
example {α β : Type} (f : α → β) (hc : ∀ a b : α, a = b → f a = f b) (a b : α) (h : a = b) :
    f a = f b := by
  apply hc
  exact h

/-! ### R4. `funext x` (lemma `funext`) · goal `f = g` → context gains `x`, goal `f x = g x`
`funext : (∀ x, f x = g x) → f = g` is function extensionality (a theorem in Lean 4, proved from
`Quot.sound`). Term form: `funext fun x => (proof of f x = g x)`. When `f`, `g` are `fun`-terms the
goal shows their bodies with `x` substituted. -/
example {α β : Type} (f g : α → β) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-! ### R5. `apply propext` (axiom `propext`) · goal `A = B` between propositions → `A ↔ B`
`propext : (A ↔ B) → A = B` (propositional extensionality, one of the two allowed axioms). Term form:
`propext ⟨fun a => (proof of B), fun b => (proof of A)⟩`. -/
example (A B : Prop) (h : A ↔ B) : A = B := by
  apply propext
  exact h

/-! ### R6. `.inl` / `.inr` (`Or.inl`, `Or.inr`) · goal `A ∨ B` → `A` (left) or `B` (right)
`refine .inr ?_` picks the right side and leaves it as the goal; `exact .inr hb` does it in one go.
The leading dot means `Or.inr`, found from the expected type `A ∨ B`. -/
example (A B : Prop) (hb : B) : A ∨ B := by
  refine .inr ?_
  exact hb

/-! ## Case analysis on what the choice operator promises -/

/-! ### R7. `⟨a, ?_⟩` (anonymous constructor for `∃`) · goal `∃ x, P x` → `P a`
`⟨a, ha⟩` builds `∃ x, P x` from a witness `a` and `ha : P a`; `refine ⟨a, ?_⟩` leaves `P a` as the
goal. Inside a `have`: `have h : ∃ x, x = a ∨ B := ⟨a, .inl rfl⟩`. -/
example {α : Type} (P : α → Prop) (a : α) (ha : P a) : ∃ x, P x := by
  refine ⟨a, ?_⟩
  exact ha

/-! ### R8. `rcases e with h | h` · goal list: one goal per side of `e : A ∨ B`
`e` may be any term, such as a hypothesis applied to an argument (`hs a`). An `_` argument is filled
in by unification from the other arguments' types. -/
example (A B C G : Prop) (hs : A → B ∨ C) (a : A) (hB : B → G) (hC : C → G) : G := by
  rcases hs a with h | h
  · exact hB h
  · exact hC h

/-! ### R9. `intro h` on `¬A` · goal `¬A` → context gains `h : A`, goal `False`
`¬A` is `A → False`, so `intro` works on it; `fun h => (proof of False)` is the term form. -/
example (A : Prop) (h' : A → False) : ¬A := by
  intro h
  exact h' h

/-! ### R10. `have := e` · context gains `this : T`, where `T` is the type of `e` -/
example (A G : Prop) (f : A → G) (a : A) : G := by
  have := f a
  exact this

/-! ### R11. `rw [h₁, h₂] at h` · context: hypothesis `h` rewritten (goal unchanged) -/
example {α : Type} (a b c d : α) (h₁ : a = c) (h₂ : b = d) (h : a = b) (G : Prop)
    (g : c = d → G) : G := by
  rw [h₁, h₂] at h
  exact g h

/-! ### R12. `Bool.noConfusion h` · closes any goal from `h : true = false`
Distinct constructors of an inductive type are never equal; `Bool.noConfusion` turns the impossible
equation into a proof of whatever the goal is. -/
example (G : Prop) (h : true = false) : G := by
  exact Bool.noConfusion h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A function with a proof argument respects equality: R1, then R2 -/
example (pick : (n : Nat) → n ≠ 0 → Nat) (n m : Nat) (hn : n ≠ 0) (hm : m ≠ 0) (h : n = m) :
    pick n hn = pick m hm := by
  subst h
  rfl

/-! ### W2. Two predicates are equal when they agree on every input: R4, R5 -/
example (q : Prop) (hq : q) : (fun n : Nat => n < 3 ∧ q) = (fun n => n < 3) := by
  funext n
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, hq⟩⟩

/-! ### W3. "`q` would force `true = false`", so `¬q`: R9, R10, R11, R12 -/
example (q : Prop) (f : Nat → Bool) (hq : q → f 0 = f 1) (h0 : f 0 = true) (h1 : f 1 = false) :
    ¬q := by
  intro hq'
  have := hq hq'
  rw [h0, h1] at this
  exact Bool.noConfusion this

end H003Guide

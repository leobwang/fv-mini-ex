/- Guide for E008 (Not and False).
Part R: one reference entry per tactic or term the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`A B C D G : Prop` are arbitrary propositions; `G` is "any goal" when the step does not look at it.
A hypothesis `k` in an entry is only there to finish the example; it shows what the goal became.
The one fact behind every entry: `¬A` is DEFINED as `A → False`, so a proof of `¬A` is a function
that turns a proof of `A` into a proof of `False`, and `False` (the proposition with no proof) is
reached only by applying such a function.
Part W: worked combinations on propositions that are NOT the exercise's.
Assumed: E003 (`intro`, `exact`, `apply`), E004 (`fun`, `⟨_, _⟩`), E005 (`constructor`,
`rintro ⟨_, _⟩`, `↔`, `·`) and E006 (`Or.inl`, `Or.inr`, the pattern `a | b`).
-/

namespace E008Guide

/-! # Part R · Reference entries -/

/-! ## Proving a negation -/

/-! ### R1. `intro h` on `¬A` · goal `¬A` → `False`; context gains `h : A`
`¬A` unfolds to `A → False`, so `intro` works on it exactly as on an implication (E003). -/
example (A : Prop) (k : A → False) : ¬A := by
  intro h
  exact k h

/-! ### R2. `exact hn ha` · closes `False` from `hn : ¬A` and `ha : A`
`hn : A → False` is a function; applied to `ha : A` it gives `hn ha : False`. -/
example (A : Prop) (ha : A) (hn : ¬A) : False := by
  exact hn ha

/-! ### R3. `rintro ⟨ha, hb⟩` on `¬(A ∧ B)` · goal → `False`; context gains `ha : A`, `hb : B`
One step: `intro` the `A ∧ B` (it is the argument of the hidden `→ False`) and split it (E005). -/
example (A B : Prop) (k : A → B → False) : ¬(A ∧ B) := by
  rintro ⟨ha, hb⟩
  exact k ha hb

/-! ### R4. `contradiction` · closes ANY goal when the context holds `A` and `¬A` (or `False`)
It searches the context for a clash itself; you name nothing. -/
example (A G : Prop) (ha : A) (hn : ¬A) : G := by
  contradiction

/-! ### R5. `intro h1 h2 h3` through a trailing `¬` · context gains all three names
`A → B → ¬C` is `A → B → C → False`: the last name takes the `C` hidden inside `¬C`, and the goal
becomes `False`. -/
example (A B C : Prop) (k : A → B → C → False) : A → B → ¬C := by
  intro ha hb hc
  exact k ha hb hc

/-! ### R6. `exact hnb (hab ha)` · closes `False` by chaining two functions
`hab ha : B`, then `hnb (hab ha) : False`. Read nested applications inside out. -/
example (A B : Prop) (hab : A → B) (hnb : ¬B) (ha : A) : False := by
  exact hnb (hab ha)

/-! ## Using a clash to prove anything -/

/-! ### R7. `exfalso` · goal `G` → `False` (context unchanged)
From `False` anything follows, so to prove any `G` it suffices to prove `False`. -/
example (G : Prop) (k : False) : G := by
  exfalso
  exact k

/-! ### R8. `absurd ha hn` · closes ANY goal `G`; `absurd : a → ¬a → b`
The term version of R7 + R2 in one call: the first argument proves `A`, the second `¬A`. -/
example (A G : Prop) (ha : A) (hn : ¬A) : G := by
  exact absurd ha hn

/-! ## Building `↔`, `∧`, `∨` around negations -/

/-! ### R9. `constructor` on `A ↔ B` · goal list: `A → B`, then `B → A` (E005)
The two goals are named `mp` (→) and `mpr` (←); focus each with `·`. -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  · exact hab
  · exact hba

/-! ### R10. `fun ha => e` · closes `¬A` as a term, where `e : False` may use `ha : A`
The term-mode twin of R1: a proof of `A → False` is a function (E004). -/
example (A : Prop) (k : A → False) : ¬A := by
  exact fun ha => k ha

/-! ### R11. `Or.inl ha : A ∨ B`, `Or.inr hb : A ∨ B` · terms that build an `∨` (E006)
Use them as arguments: `h (Or.inl ha) : False` when `h : ¬(A ∨ B)`. -/
example (A B : Prop) (ha : A) : A ∨ B := by
  exact Or.inl ha

example (A B : Prop) (hb : B) : A ∨ B := by
  exact Or.inr hb

/-! ### R12. `exact ⟨e₁, e₂⟩` · closes `A ∧ B` from `e₁ : A`, `e₂ : B` (any terms, lambdas too) -/
example (A B : Prop) (ka : A → False) (kb : B → False) : ¬A ∧ ¬B := by
  exact ⟨fun ha => ka ha, fun hb => kb hb⟩

/-! ### R13. `rintro (hc | hd)` on `¬(C ∨ D)` · goal list: one `False` goal per side of the `∨`
`intro` the `C ∨ D` and split it by cases (pattern `a | b`, E006): first goal has `hc : C`, second
`hd : D`. The goals are named `inl` and `inr`. -/
example (C D : Prop) (kc : C → False) (kd : D → False) : ¬(C ∨ D) := by
  rintro (hc | hd)
  · exact kc hc
  · exact kd hd

/-! # Part W · Worked combinations (not the exercise's propositions) -/

/-! ### W1. `¬A` really is `A → False`: R9, then R1 / R2 in each direction -/
example (A : Prop) : ¬A ↔ (A → False) := by
  constructor
  · intro h ha
    exact h ha
  · intro h ha
    exact h ha

/-! ### W2. A weaker conjunction is still refuted: R3, then R2 -/
example (A B : Prop) (hna : ¬A) : ¬(A ∧ B) := by
  rintro ⟨ha, hb⟩
  exact hna ha

/-! ### W3. Triple negation: R5, then R6 with a lambda (R10) as the inner argument -/
example (A : Prop) : ¬¬¬A → ¬A := by
  intro h ha
  exact h (fun hn => hn ha)

/-! ### W4. A function that returns a negation, applied fully: R7, then R2 with `hn := h hna`
`h hna : ¬B`, so `h hna hb : False`: arguments are supplied left to right. -/
example (A B C : Prop) (h : ¬A → ¬B) (hna : ¬A) (hb : B) : C := by
  exfalso
  exact h hna hb

/-! ### W5. One `rintro` with two patterns, one per arrow: R3's `∧` pattern, then R13's `∨` pattern
Each side of the `∨` gets its own goal; close each with R11 and R12. -/
example (A B C D : Prop) : A ∧ B → C ∨ D → (A ∧ C) ∨ (B ∧ D) := by
  rintro ⟨ha, hb⟩ (hc | hd)
  · exact Or.inl ⟨ha, hc⟩
  · exact Or.inr ⟨hb, hd⟩

end E008Guide

/- Guide for E025 (Bounded quantifiers).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is a goal the step does not touch (the step changes the context instead).
Part W: worked combinations on other lists, maps and bounds than the exercise's.
Assumed: Lean basics up to E024 (`intro`, `exact`, `obtain`, `rcases`, `rw … at`, `omega`, `decide`).
-/

namespace E025Guide

/-! # Part R · Reference entries -/

/-! ## Using `∀ x ∈ l, …`: introduce, then read the membership -/

/-! ### R1. `intro y hy` · goal `∀ y ∈ l, P y` → `P y`; context gains `y` and `hy : y ∈ l`
`∀ y ∈ l, P y` is notation for `∀ y, y ∈ l → P y`, so `intro` takes two names. -/
example {α : Type} (l : List α) (P : α → Prop) (h : ∀ y, y ∈ l → P y) : ∀ y ∈ l, P y := by
  intro y hy
  exact h y hy

/-! ### R2. `rw [List.mem_map] at hy` · context: `hy : b ∈ List.map f l` → `∃ a ∈ l, f a = b`
`List.mem_map : b ∈ List.map f l ↔ ∃ a, a ∈ l ∧ f a = b`. `rw` with an `↔` rewrites propositions. -/
example {α β : Type} (f : α → β) (l : List α) (b : β) (G : Prop) (hy : b ∈ List.map f l)
    (k : (∃ a ∈ l, f a = b) → G) : G := by
  rw [List.mem_map] at hy
  exact k hy

/-! ### R3. `obtain ⟨a, ha, rfl⟩ := hy` · context: `hy` → `a`, `ha : a ∈ l`; `b` replaced by `f a`
The pattern `rfl` for the equation `f a = b` substitutes `b := f a` everywhere, the goal included,
and removes `b` from the context. -/
example {α β : Type} (f : α → β) (l : List α) (b : β) (P : β → Prop)
    (k : ∀ a, a ∈ l → P (f a)) (hy : ∃ a ∈ l, f a = b) : P b := by
  obtain ⟨a, ha, rfl⟩ := hy
  exact k a ha

/-! ### R4. `have := h a ha` · context gains `this : P a`
A proof `h : ∀ x ∈ l, P x` is a function: give it an element and a membership proof. Without a name,
`have` calls the new fact `this`. -/
example {α : Type} (l : List α) (P : α → Prop) (G : Prop) (h : ∀ x ∈ l, P x) (a : α)
    (ha : a ∈ l) (k : P a → G) : G := by
  have := h a ha
  exact k this

/-! ### R5. `omega` · closes linear `Nat` arithmetic, using the hypotheses in the context
`a * 3` counts as linear: one side of the product is a literal. -/
example (a : Nat) (this : a > 0) : a * 3 > 2 := by
  omega

/-! ## Membership in `++` and a case split -/

/-! ### R6. `rw [List.mem_append] at hz` · context: `hz : c ∈ s ++ t` → `c ∈ s ∨ c ∈ t`
`List.mem_append : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`. -/
example {α : Type} (s t : List α) (c : α) (G : Prop) (hz : c ∈ s ++ t)
    (k : c ∈ s ∨ c ∈ t → G) : G := by
  rw [List.mem_append] at hz
  exact k hz

/-! ### R7. `rcases hz with hz | hz` · goal list: one goal → two, one per side of `∨`
Each goal keeps the name `hz` for the side it got. -/
example {α : Type} (s t : List α) (c : α) (P : α → Prop) (hs : c ∈ s → P c) (ht : c ∈ t → P c)
    (hz : c ∈ s ∨ c ∈ t) : P c := by
  rcases hz with hz | hz
  · exact hs hz
  · exact ht hz

/-! ### R8. `exact h a ha` · closes `P a` from `h : ∀ x ∈ l, P x` and `ha : a ∈ l` (R4 as a closer) -/
example {α : Type} (l : List α) (P : α → Prop) (h : ∀ x ∈ l, P x) (a : α) (ha : a ∈ l) : P a := by
  exact h a ha

/-! ## Proving `∃ x ∈ l, …` -/

/-! ### R9. `refine ⟨a, ?_, ?_⟩` · goal `∃ x ∈ l, P x` → two goals `a ∈ l` and `P a`
`∃ x ∈ l, P x` is notation for `∃ x, x ∈ l ∧ P x`; the anonymous constructor `⟨a, hm, hp⟩` fills the
witness `a`, the membership proof `hm` and the proof `hp` in one go (it also works as a term). -/
example {α : Type} (l : List α) (P : α → Prop) (a : α) (hm : a ∈ l) (hp : P a) :
    ∃ x ∈ l, P x := by
  refine ⟨a, ?_, ?_⟩
  · exact hm
  · exact hp

/-! ### R10. `apply List.mem_cons.mpr` · goal `a ∈ b :: l` → `a = b ∨ a ∈ l`
`List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`; `.mpr` is its right-to-left direction, a function from
`a = b ∨ a ∈ l` to `a ∈ b :: l`. `rw [List.mem_cons]` gives the same goal. -/
example {α : Type} (a b : α) (l : List α) (h : a = b ∨ a ∈ l) : a ∈ b :: l := by
  apply List.mem_cons.mpr
  exact h

/-! ### R11. `exact Or.inr h` · closes `A ∨ B` from `h : B` (`Or.inl` for the left side) -/
example (A B : Prop) (h : B) : A ∨ B := by
  exact Or.inr h

/-! ### R12. `decide` · closes a comparison of two `Nat` literals -/
example : 7 > 4 := by
  decide

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Through a `map` with no hypothesis: R1, R2, R3, then R5 -/
example (xs : List Nat) : ∀ y ∈ xs.map (· + 3), y ≥ 3 := by
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  omega

/-! ### W2. A witness at the head of the list: R9, R10, then `Or.inl rfl`, R12 -/
example (xs : List Nat) : ∃ x ∈ 5 :: xs, x > 4 := by
  refine ⟨5, ?_, ?_⟩
  · apply List.mem_cons.mpr
    exact Or.inl rfl
  · decide

end E025Guide

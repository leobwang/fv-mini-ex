/- Guide for M070 (Image and preimage).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's (intersections of images,
preimages of unions and complements, plain set algebra).
Assumed: Lean basics (E001–E033), in particular `∧`, `∨`, `↔`, `∃`, `rintro`/`obtain` patterns.
-/
import Mathlib

namespace M070Guide

/-! # Part R · Reference entries -/

/-! ## Set equations → membership -/

/-! ### R1. `ext x` (lemma `Set.ext`) · goal `s = t` → context gains `x`, goal `x ∈ s ↔ x ∈ t` -/
example {α : Type} (s t : Set α) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

/-! ### R2. `constructor` on `↔` · goal list: `A ↔ B` → `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exacts [hab, hba]

/-! ## Images -/

/-! ### R3. `Set.mem_image` · `b ∈ f '' s ↔ ∃ x ∈ s, f x = b` · goal
`∃ x ∈ s, Q x` is notation for `∃ x, x ∈ s ∧ Q x`. Holds by definition, so you rarely `rw` it: patterns and `⟨…⟩` see through it directly (R5, R8). -/
example {α β : Type} (f : α → β) (s : Set α) (b : β) (h : ∃ x ∈ s, f x = b) : b ∈ f '' s := by
  rw [Set.mem_image]
  exact h

/-! ### R4. `Set.mem_union` · `a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t` · goal (also definitional) -/
example {α : Type} (s t : Set α) (a : α) (h : a ∈ s ∨ a ∈ t) : a ∈ s ∪ t := by
  rw [Set.mem_union]
  exact h

/-! ### R5. `rintro ⟨x, hx, rfl⟩` on `y ∈ f '' s → …` · context: `y` is replaced by `f x`
The pattern `rfl` consumes `f x = y` by substituting `f x` for the variable `y` everywhere. -/
example {α β : Type} (f : α → β) (s : Set α) (P : β → Prop) (h : ∀ x ∈ s, P (f x)) (y : β) :
    y ∈ f '' s → P y := by
  rintro ⟨x, hx, rfl⟩
  exact h x hx

/-! ### R6. `rintro (ha | hb)` on `a ∈ s ∪ t → …` · goal list: one goal per side of the union
Nested inside an image pattern it reads `⟨x, hx | hx, rfl⟩`: one goal per side, each with its `x`. -/
example {α : Type} (s t : Set α) (a : α) (P : Prop) (hs : a ∈ s → P) (ht : a ∈ t → P) :
    a ∈ s ∪ t → P := by
  rintro (ha | hb)
  exacts [hs ha, ht hb]

/-! ### R7. `refine Or.inl ?_` / `refine Or.inr ?_` · goal: `a ∈ s ∪ t` → `a ∈ s` / `a ∈ t` -/
example {α : Type} (s t : Set α) (a : α) (ha : a ∈ s) : a ∈ s ∪ t := by
  refine Or.inl ?_
  exact ha

example {α : Type} (s t : Set α) (a : α) (ha : a ∈ t) : a ∈ s ∪ t := by
  refine Or.inr ?_
  exact ha

/-! ### R8. `refine ⟨x, ?_, rfl⟩` on `f x ∈ f '' s` · goal → `x ∈ s`
Witness `x`, the `rfl` proves `f x = f x`; `exact ⟨x, hx, rfl⟩` does all three at once. -/
example {α β : Type} (f : α → β) (s : Set α) (x : α) (hx : x ∈ s) : f x ∈ f '' s := by
  refine ⟨x, ?_, rfl⟩
  exact hx

/-! ## Subsets and preimages -/

/-! ### R9. `intro x hx` on `s ⊆ t` (lemma `Set.subset_def`) · context gains `x`, `hx : x ∈ s`; goal `x ∈ t`
`s ⊆ t` means `∀ x ∈ s, x ∈ t`, i.e. `∀ x, x ∈ s → x ∈ t`, so it is proved like a `∀`/`→` (also by `fun x hx => …`). -/
example {α : Type} (s t : Set α) (h : ∀ x ∈ s, x ∈ t) : s ⊆ t := by
  intro x hx
  exact h x hx

/-! ### R10. `Set.mem_preimage` · `a ∈ f ⁻¹' s ↔ f a ∈ s` · goal (definitional: `exact` sees through it) -/
example {α β : Type} (f : α → β) (s : Set β) (a : α) (h : f a ∈ s) : a ∈ f ⁻¹' s := by
  rw [Set.mem_preimage]
  exact h

example {α β : Type} (f : α → β) (s : Set β) (a : α) (h : a ∈ f ⁻¹' s) : f a ∈ s := by
  exact h

/-! ### R11. `Set.mem_inter_iff` · `a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t` · goal (also definitional) -/
example {α : Type} (s t : Set α) (a : α) (h : a ∈ s ∧ a ∈ t) : a ∈ s ∩ t := by
  rw [Set.mem_inter_iff]
  exact h

/-! ### R12. `rfl` on `A ↔ B` · closes the goal when both sides unfold to the same proposition -/
example {α : Type} (s t : Set α) (a : α) : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := by
  rfl

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Image of an intersection: unpack with R5 (a `∧` inside), rebuild with R8 twice -/
example {α β : Type} (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨hs, ht⟩, rfl⟩
  exact ⟨⟨x, hs, rfl⟩, ⟨x, ht, rfl⟩⟩

/-! ### W2. Preimage of a union: R1, then R12 (both sides unfold to `f x ∈ s ∨ f x ∈ t`) -/
example {α β : Type} (f : α → β) (s t : Set β) : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := by
  ext x
  rfl

/-! ### W3. A nested `|` pattern without images: R9-style `rintro` with R6 inside, then R7 -/
example {α : Type} (s t u : Set α) : (s ∪ t) ∩ u ⊆ (s ∩ u) ∪ (t ∩ u) := by
  rintro x ⟨hs | ht, hu⟩
  · exact Or.inl ⟨hs, hu⟩
  · exact Or.inr ⟨ht, hu⟩

/-! ### W4. Preimage of a complement, by R9 and R10 in term mode -/
example {α β : Type} (f : α → β) (s : Set β) : (f ⁻¹' s)ᶜ ⊆ f ⁻¹' sᶜ :=
  fun _ hx => hx

end M070Guide

/- Guide for E040 (Set extensionality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `G` stand for "the rest of your goal". A hypothesis `g` in an entry is only there to finish the
example; it shows what the goal or context became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `intro`, `exact`, `constructor`, `rintro`, `⟨_, _⟩`, `Or.inl`, `omega`.
Mathlib's `Set α` is `α → Prop`: a set is the predicate "is a member". `x ∈ s` unfolds to `s x`, and
`∩`, `∪`, `⊆`, `{x | p x}` all unfold to logic (`∧`, `∨`, `∀ x, x ∈ s → x ∈ t`, `p x`).
-/
import Mathlib

namespace E040Guide

/-! # Part R · Reference entries -/

/-! ## Equal sets: same members -/

/-! ### R1. `ext x` (lemma `Set.ext`) · goal `s = t` → context gains `x`, goal `x ∈ s ↔ x ∈ t`
`Set.ext : (∀ x, x ∈ s ↔ x ∈ t) → s = t`. -/
example {α : Type} (s t : Set α) (g : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact g x

/-! ### R2. `Set.mem_inter_iff` · `a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t` · goal: membership in `∩` → `∧` -/
example {α : Type} (s t : Set α) (x : α) (P : Prop → Prop) (g : P (x ∈ s ∧ x ∈ t)) :
    P (x ∈ s ∩ t) := by
  simp only [Set.mem_inter_iff]
  exact g

/-! ### R3. `constructor` on `A ↔ B` · goal list: one goal → `A → B` and `B → A` -/
example (A B : Prop) (gab : A → B) (gba : B → A) : A ↔ B := by
  constructor
  exact gab
  exact gba

/-! ### R4. `rintro ⟨ha, hb⟩` · goal `A ∧ B → G` → context gains `ha : A`, `hb : B`, goal `G` -/
example (A B G : Prop) (g : A → B → G) : A ∧ B → G := by
  rintro ⟨ha, hb⟩
  exact g ha hb

/-! ### R5. `exact ⟨hb, ha⟩` · closes `B ∧ A` from its two halves (anonymous constructor `And.intro`) -/
example (A B : Prop) (ha : A) (hb : B) : B ∧ A := by
  exact ⟨hb, ha⟩

/-! ## Subsets: chase one element -/

/-! ### R6. `intro x hx` on `s ⊆ t` · context gains `x : α`, `hx : x ∈ s`; goal `x ∈ t`
`s ⊆ t` is by definition `∀ ⦃a⦄, a ∈ s → a ∈ t`, so `intro` sees through it. -/
example {α : Type} (s t : Set α) (g : ∀ y, y ∈ s → y ∈ t) : s ⊆ t := by
  intro x hx
  exact g x hx

/-! ### R7. `Set.mem_union` · `a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t` · goal: membership in `∪` → `∨` -/
example {α : Type} (s t : Set α) (x : α) (P : Prop → Prop) (g : P (x ∈ s ∨ x ∈ t)) :
    P (x ∈ s ∪ t) := by
  simp only [Set.mem_union]
  exact g

/-! ### R8. `Or.inl h` / `Or.inr h` · closes `x ∈ s ∪ t` with no rewrite
`x ∈ s ∪ t` is by definition `x ∈ s ∨ x ∈ t`, so the `∨` constructors are accepted as they are. -/
example {α : Type} (s t : Set α) (x : α) (ht : x ∈ t) : x ∈ s ∪ t := by
  exact Or.inr ht

/-! ### R9. `rintro x ⟨hs, ht⟩` on `s ∩ t ⊆ u` · context gains `x`, `hs : x ∈ s`, `ht : x ∈ t`
One step for R6 and R4: `x ∈ s ∩ t` is by definition `x ∈ s ∧ x ∈ t`, so the pattern splits it. -/
example {α : Type} (s t u : Set α) (g : ∀ y, y ∈ s → y ∈ t → y ∈ u) : s ∩ t ⊆ u := by
  rintro x ⟨hs, ht⟩
  exact g x hs ht

/-! ### R10. `h hs` for `h : s ⊆ t` · context gains `hx : x ∈ t` from `hs : x ∈ s`
The element is an implicit argument `⦃a⦄` of `h`: write `h hs`, not `h x hs`. -/
example {α : Type} (s t : Set α) (x : α) (h : s ⊆ t) (hs : x ∈ s) (G : Prop) (g : x ∈ t → G) :
    G := by
  have hx := h hs
  exact g hx

/-! ### R11. `exact ⟨hs, ht⟩` · closes `x ∈ s ∩ t` with no rewrite (it is `x ∈ s ∧ x ∈ t`) -/
example {α : Type} (s t : Set α) (x : α) (hs : x ∈ s) (ht : x ∈ t) : x ∈ s ∩ t := by
  exact ⟨hs, ht⟩

/-! ## Set-builder and finite sets -/

/-! ### R12. `Set.mem_setOf_eq` · `(a ∈ {x | p x}) = p a` · goal: membership → the predicate -/
example {α : Type} (p : α → Prop) (x : α) (P : Prop → Prop) (g : P (p x)) :
    P (x ∈ {y | p y}) := by
  simp only [Set.mem_setOf_eq]
  exact g

/-! ### R13. `Set.mem_insert_iff` · `a ∈ insert b s ↔ a = b ∨ a ∈ s`
`{a, b, c}` is notation for `insert a (insert b {c})`, so this peels off one listed element. -/
example {α : Type} (s : Set α) (x b : α) (P : Prop → Prop) (g : P (x = b ∨ x ∈ s)) :
    P (x ∈ insert b s) := by
  simp only [Set.mem_insert_iff]
  exact g

/-! ### R14. `Set.mem_singleton_iff` · `a ∈ {b} ↔ a = b` · goal: membership in `{b}` → equation -/
example {α : Type} (x b : α) (P : Prop → Prop) (g : P (x = b)) : P (x ∈ ({b} : Set α)) := by
  simp only [Set.mem_singleton_iff]
  exact g

/-! ### R15. `omega` · closes a linear `ℕ` goal built with `↔`, `∨`, `∧`, `=`, `<` -/
example (n : ℕ) : n < 2 ↔ n = 0 ∨ n = 1 := by
  omega

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1, R7, then `Or.comm`: `∪` is symmetric -/
example {α : Type} (s t : Set α) : s ∪ t = t ∪ s := by
  ext x
  simp only [Set.mem_union]
  exact Or.comm

/-! ### W2. R9 then R8: an element of `s ∩ t` is in `s ∪ t` -/
example {α : Type} (s t : Set α) : s ∩ t ⊆ s ∪ t := by
  rintro x ⟨hs, ht⟩
  exact Or.inl hs

/-! ### W3. R6, R10, R8: a subset of `t` is a subset of `u ∪ t` -/
example {α : Type} (s t u : Set α) (h : s ⊆ t) : s ⊆ u ∪ t := by
  intro x hx
  exact Or.inr (h hx)

/-! ### W4. R1, R12–R14, R15 on a two-element set -/
example : {n : ℕ | n < 2} = {0, 1} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

end E040Guide

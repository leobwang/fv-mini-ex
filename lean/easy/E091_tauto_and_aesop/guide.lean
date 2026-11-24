/- Guide for E091 (tauto and aesop).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E091Guide

/-! # Part R · Reference entries -/

/-! ## Propositional logic: `tauto` -/

/-! ### R1. `tauto` · closes a tautology built from `→`, `∧`, `∨`, `True`, `False`
Works on the connectives only: the propositions `A B : Prop` are opaque letters to it. It splits
hypotheses and goal, introduces `→`, and tries every case of an `∨`. -/
example (A B : Prop) : A ∧ B → B ∧ A := by
  tauto

/-! ### R2. `tauto` with `¬` and `↔` · closes it; classical (may use `A ∨ ¬A`)
`¬A` is `A → False`; `A ↔ B` is split into `A → B` and `B → A`. This law needs excluded middle. -/
example (A B : Prop) : ¬(A ∧ B) ↔ ¬A ∨ ¬B := by
  tauto

/-! ## Quantifiers and membership: `aesop` -/

/-! ### R3. `aesop` · closes goals that also need `∀`: it introduces `∀`/`→`, splits `∧`,
instantiates `∀` hypotheses, and normalises with Mathlib's simplification lemmas (`@[simp]`). -/
example {α : Type} (p q : α → Prop) (hpq : ∀ x, p x → q x) (hp : ∀ x, p x) : ∀ x, q x := by
  aesop

/-! ### R4. `List.mem_append` · `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` · goal: membership in `++` → `∨`
`aesop` applies this one by itself (it is a `@[simp]` lemma). -/
example {α : Type} (a : α) (s t : List α) (h : a ∈ s ∨ a ∈ t) : a ∈ s ++ t := by
  rw [List.mem_append]
  exact h

/-! ### R5. `aesop` on bounded quantifiers · closes it
`∀ x ∈ l, P x` means `∀ x, x ∈ l → P x`. `aesop` introduces `x` and `x ∈ l`, rewrites the
membership with R4, and splits the resulting `∨` into one case per list. -/
example {α : Type} (P : α → Prop) (l₁ l₂ : List α) (h₁ : ∀ x ∈ l₁, P x) (h₂ : ∀ x ∈ l₂, P x) :
    ∀ x ∈ l₁ ++ l₂, P x := by
  aesop

/-! ## Sets: unfolding `⊆` for `aesop` -/

/-! ### R6. `Set.subset_def` · `(s ⊆ t) = ∀ x ∈ s, x ∈ t` · goal: `⊆` → a bounded `∀`
`Set α` is "predicates on `α`"; `x ∈ s` says `x` satisfies `s`. -/
example {α : Type} (s t : Set α) (h : ∀ x ∈ s, x ∈ t) : s ⊆ t := by
  rw [Set.subset_def]
  exact h

/-! ### R7. `Set.mem_inter_iff` · `x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b` · goal: `∈ ∩` → `∧`
`aesop` applies this one by itself (it is a `@[simp]` lemma). -/
example {α : Type} (x : α) (s t : Set α) (h : x ∈ s ∧ x ∈ t) : x ∈ s ∩ t := by
  rw [Set.mem_inter_iff]
  exact h

/-! ### R8. `aesop (add norm L)` · closes it, now that `aesop` may also rewrite with the equation `L`
Plain `aesop` treats `s ⊆ t` as opaque here and makes no progress. With `L := Set.subset_def`
it turns every `⊆` (goal and hypotheses) into a `∀`, and R3 takes over. -/
example {α : Type} (s t u : Set α) (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  aesop (add norm Set.subset_def)

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. `tauto` does case analysis on `∨` (R1) -/
example (A B C : Prop) : A ∨ B → (A → C) → (B → C) → C := by
  tauto

/-! ### W2. What `aesop (add norm Set.subset_def)` does, by hand: R6, `intro`, R7, then `exact`
On `s ∩ t ⊆ t ∩ s`. Each step below is one that `aesop` finds by itself. -/
example {α : Type} (s t : Set α) : s ∩ t ⊆ t ∩ s := by
  rw [Set.subset_def]
  intro x hx
  rw [Set.mem_inter_iff] at hx
  rw [Set.mem_inter_iff]
  exact ⟨hx.2, hx.1⟩

/-! ### W3. The same goal in one step (R8) -/
example {α : Type} (s t : Set α) : s ∩ t ⊆ t ∩ s := by
  aesop (add norm Set.subset_def)

end E091Guide

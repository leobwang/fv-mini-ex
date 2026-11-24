/- Guide for H039 (Knaster–Tarski).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`α` is any type, `a b c t : Set α` are sets of elements of `α`, `S : Set (Set α)` is a family of
such sets, `g : Set α → Set α` is a map on sets (it plays the role of `f`).
Part W: worked combinations on objects that are NOT the exercise's (a family with a least member,
an arbitrary family `S`, the sets below a fixed `b`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H039Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · `lfp_least`: the intersection is below each of its members -/

/-! ### R1. `unfold D` · goal: the defined name `D` → its body
Optional: `exact`/`apply` see through a `def` by themselves; `unfold` only makes the goal readable. -/
def bigInter {α : Type} (S : Set (Set α)) : Set α := ⋂₀ S

example {α : Type} (S : Set (Set α)) (P : Set α → Prop) (h : P (⋂₀ S)) : P (bigInter S) := by
  unfold bigInter
  exact h

/-! ### R2. `Set.sInter_subset_of_mem` · `t ∈ S → ⋂₀ S ⊆ t` · goal `⋂₀ S ⊆ t` → `t ∈ S`
`⋂₀ S` is the intersection of all sets in the family `S`. -/
example {α : Type} (S : Set (Set α)) (t : Set α) (h : t ∈ S) : ⋂₀ S ⊆ t := by
  apply Set.sInter_subset_of_mem
  exact h

/-! ### R3. `Set.mem_setOf_eq` · `(a ∈ {x | p x}) = p a` · goal: membership → the property
`{x | p x}` is notation for `setOf p`. Membership in it *is* `p a` by definition, so `exact h` also
works without this step. W3 shows it on `{X | X ⊆ b}`. -/
example {α : Type} (p : Set α → Prop) (a : Set α) (h : p a) : a ∈ setOf p := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ## Part 2 · `lfp_fixed`: two inclusions -/

/-! ### R4. `subset_antisymm` · `a ⊆ b → b ⊆ a → a = b` · goal list: `a = b` → `a ⊆ b`, `b ⊆ a` -/
example {α : Type} (a b : Set α) (h1 : a ⊆ b) (h2 : b ⊆ a) : a = b := by
  apply subset_antisymm
  exact h1
  exact h2

/-! ### R5. `Set.subset_sInter` · `(∀ t' ∈ S, t ⊆ t') → t ⊆ ⋂₀ S` · goal: below the intersection →
below every member -/
example {α : Type} (S : Set (Set α)) (t : Set α) (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ ⋂₀ S := by
  apply Set.subset_sInter
  exact h

/-! ### R6. `intro A hA` on `∀ t' ∈ S, Q t'` · context gains `A` and `hA : A ∈ S`
`∀ t' ∈ S, Q t'` is short for `∀ t', t' ∈ S → Q t'`, so it takes two names. -/
example {α : Type} (S : Set (Set α)) (b : Set α) (h : ∀ t' ∈ S, b ⊆ t') :
    ∀ t' ∈ S, b ⊆ t' := by
  intro A hA
  exact h A hA

/-! ### R7. `HasSubset.Subset.trans` (`h1.trans`) · `a ⊆ b → b ⊆ c → a ⊆ c` · goal `a ⊆ c` → `b ⊆ c`
In term mode: `h1.trans h2 : a ⊆ c`. -/
example {α : Type} (a b c : Set α) (h1 : a ⊆ b) (h2 : b ⊆ c) : a ⊆ c := by
  refine h1.trans ?_
  exact h2

/-! ### R8. A monotonicity hypothesis `hg : ∀ A B, A ⊆ B → g A ⊆ g B` · goal `g a ⊆ g b` → `a ⊆ b`
In term mode: `hg _ _ h : g a ⊆ g b` for `h : a ⊆ b`. A hypothesis whose type is a `def` that unfolds to
this `∀` (as `hf : Mono f` does) is used in exactly the same way. -/
example {α : Type} (g : Set α → Set α) (a b : Set α) (hg : ∀ A B, A ⊆ B → g A ⊆ g B)
    (h : a ⊆ b) : g a ⊆ g b := by
  apply hg
  exact h

/-! ## Part 3 · `gfp_greatest`: each member is below the union -/

/-! ### R9. `Set.subset_sUnion_of_mem` · `t ∈ S → t ⊆ ⋃₀ S` · goal `t ⊆ ⋃₀ S` → `t ∈ S`
`⋃₀ S` is the union of all sets in the family `S`. -/
example {α : Type} (S : Set (Set α)) (t : Set α) (h : t ∈ S) : t ⊆ ⋃₀ S := by
  apply Set.subset_sUnion_of_mem
  exact h

/-! ## Part 4 · `gfp_fixed`: the dual of Part 2 -/

/-! ### R10. `Set.sUnion_subset` · `(∀ t' ∈ S, t' ⊆ t) → ⋃₀ S ⊆ t` · goal: the union below `t` →
every member below `t` -/
example {α : Type} (S : Set (Set α)) (t : Set α) (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀ S ⊆ t := by
  apply Set.sUnion_subset
  exact h

/-! ## Part 5 · `lfp_subset_gfp`: an equation used as an inclusion -/

/-! ### R11. `Eq.le` (`h.le`) · `a = b → a ≤ b` · context gains `a ⊆ b`
On `Set α` the order `≤` is `⊆`, and Lean prints it as `⊆`. `h.ge` gives `b ⊆ a`. -/
example {α : Type} (a b : Set α) (h : a = b) : a ⊆ b := by
  have h2 := h.le
  exact h2

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A family with a least member: its intersection is that member (R4, R2, R5) -/
example {α : Type} (S : Set (Set α)) (b : Set α) (hb : b ∈ S) (hlow : ∀ t ∈ S, b ⊆ t) :
    ⋂₀ S = b := by
  apply subset_antisymm
  · apply Set.sInter_subset_of_mem
    exact hb
  · apply Set.subset_sInter
    exact hlow

/-! ### W2. Push an inclusion through a monotone map, then chain (R7, R8) -/
example {α : Type} (g : Set α → Set α) (hg : ∀ A B, A ⊆ B → g A ⊆ g B) (a b c : Set α)
    (h1 : a ⊆ b) (h2 : g b ⊆ c) : g a ⊆ c := by
  refine (hg _ _ h1).trans ?_
  exact h2

/-! ### W3. The sets below `b` have their union below `b` (R10, R6, R3) -/
example {α : Type} (b : Set α) : ⋃₀ {X | X ⊆ b} ⊆ b := by
  apply Set.sUnion_subset
  intro A hA
  rw [Set.mem_setOf_eq] at hA
  exact hA

/-! ### W4. An equation, then an inclusion into a union (R11, R7, R9) -/
example {α : Type} (S : Set (Set α)) (c d : Set α) (h : c = d) (hd : d ∈ S) : c ⊆ ⋃₀ S := by
  exact h.le.trans (Set.subset_sUnion_of_mem hd)

end H039Guide

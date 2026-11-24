/- Guide for H040 (Schröder–Bernstein).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Function

namespace H040Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · intersections of families of sets (the milestone `lfp_fixed`) -/

/-! ### R1. `apply Set.sInter_subset_of_mem` · goal `⋂₀ S ⊆ t` → `t ∈ S`
`Set.sInter_subset_of_mem : t ∈ S → ⋂₀ S ⊆ t`: the intersection of a family lies in each member. -/
example {α : Type} (S : Set (Set α)) (t : Set α) (ht : t ∈ S) : ⋂₀ S ⊆ t := by
  apply Set.sInter_subset_of_mem
  exact ht

/-! ### R2. `rw [Set.mem_setOf_eq]` · goal `a ∈ {x | Q x}` → `Q a`
The two are equal by definition, so `exact` also accepts a proof of `Q a` for `a ∈ {x | Q x}`. -/
example {α : Type} (Q : α → Prop) (a : α) (h : Q a) : a ∈ {x | Q x} := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ### R3. `apply Set.subset_sInter` · goal `s ⊆ ⋂₀ S` → `∀ t' ∈ S, s ⊆ t'`
`Set.subset_sInter : (∀ t' ∈ S, s ⊆ t') → s ⊆ ⋂₀ S`. Follow it with `intro t ht`. -/
example {α : Type} (S : Set (Set α)) (s : Set α) (h : ∀ t ∈ S, s ⊆ t) : s ⊆ ⋂₀ S := by
  apply Set.subset_sInter
  exact h

/-! ### R4. `refine h₁.trans ?_` (`HasSubset.Subset.trans`) · goal `s ⊆ u` → `t ⊆ u`
`h₁.trans h₂ : s ⊆ u` for `h₁ : s ⊆ t`, `h₂ : t ⊆ u` (transitivity of `⊆`). -/
example {α : Type} (s t u : Set α) (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u := by
  refine h₁.trans ?_
  exact h₂

/-! ### R5. `apply subset_antisymm` · goal list: `s = t` → `s ⊆ t`, `t ⊆ s`
`subset_antisymm : s ⊆ t → t ⊆ s → s = t`. -/
example {α : Type} (s t : Set α) (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t := by
  apply subset_antisymm
  exact h₁
  exact h₂

/-! ## Part 2 · the bijection -/

/-! ### R6. `classical` · goal unchanged; every `Prop` becomes decidable
Without it, `if x ∈ A then … else …` fails with "failed to synthesize Decidable (x ∈ A)". -/
example {α β : Type} (A : Set α) (u v : α → β) : ∃ k : α → β, ∀ x ∈ A, k x = u x := by
  classical
  exact ⟨fun x => if x ∈ A then u x else v x, fun x hx => if_pos hx⟩

/-! ### R7. `rcases isEmpty_or_nonempty β with hβ | hβ` · goal list: one goal → two, one per case
`isEmpty_or_nonempty β : IsEmpty β ∨ Nonempty β`. -/
example {β : Type} (G : Prop) (h0 : IsEmpty β → G) (h1 : Nonempty β → G) : G := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  exact h0 hβ
  exact h1 hβ

/-! ### R8. `refine ⟨fun a => ?_⟩` · goal `IsEmpty α` → `a : α ⊢ False`
`IsEmpty α` is a structure with one field `false : α → False`. -/
example {α β : Type} (f : α → β) (hβ : IsEmpty β) : IsEmpty α := by
  refine ⟨fun a => ?_⟩
  exact hβ.false (f a)

/-! ### R9. `exact hβ.false b` (`IsEmpty.false : IsEmpty β → β → False`) · closes `False` -/
example {β : Type} (hβ : IsEmpty β) (b : β) : False := by
  exact hβ.false b

/-! ### R10. `refine ⟨k, ?_, ?_⟩` · goal `∃ k', Bijective k'` → `Injective k`, `Surjective k`
`Bijective k` is by definition `Injective k ∧ Surjective k`, so one anonymous constructor fills the
witness and splits the `∧`. -/
example {α β : Type} (k : α → β) (h1 : Injective k) (h2 : Surjective k) :
    ∃ k' : α → β, Bijective k' := by
  refine ⟨k, ?_, ?_⟩
  exact h1
  exact h2

/-! ### R11. `exact hβ.elim b` (`IsEmpty.elim : IsEmpty β → ∀ b : β, Q b`) · closes any goal `Q b` -/
example {β : Type} (hβ : IsEmpty β) (b : β) (Q : β → Prop) : Q b := by
  exact hβ.elim b

/-! ### R12. `let F : Set α → Set α := fun S => …` · context gains `F` together with its value -/
example {α : Type} (P : (Set α → Set α) → Prop) (h : P (fun S => Sᶜ)) : P (fun S => Sᶜ) := by
  let F : Set α → Set α := fun S => Sᶜ
  exact h

/-! ### R13. `apply Set.compl_subset_compl.mpr` · goal `sᶜ ⊆ tᶜ` → `t ⊆ s`
`Set.compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s` (complement reverses `⊆`). -/
example {α : Type} (s t : Set α) (h : t ⊆ s) : sᶜ ⊆ tᶜ := by
  apply Set.compl_subset_compl.mpr
  exact h

/-! ### R14. `apply Set.image_mono` · goal `g '' s ⊆ g '' t` → `s ⊆ t`
`Set.image_mono : s ⊆ t → g '' s ⊆ g '' t`. -/
example {α β : Type} (g : α → β) (s t : Set α) (h : s ⊆ t) : g '' s ⊆ g '' t := by
  apply Set.image_mono
  exact h

/-! ### R15. `set A := e with hA` · context gains `A := e` and `hA : A = e`; `e` → `A` everywhere -/
example {α : Type} (e : Set α) (P : Set α → Prop) (h : P e) : P e := by
  set A := e with hA
  exact h

/-! ### R16. `rw [← compl_compl s]` · goal `P s` → `P sᶜᶜ`
`compl_compl s : sᶜᶜ = s`. Right to left it wraps `s` in two complements. -/
example {α : Type} (s : Set α) (P : Set α → Prop) (h : P sᶜᶜ) : P s := by
  rw [← compl_compl s]
  exact h

/-! ### R17. `have hxt : x ∈ t := e ▸ hx` · context gains `hxt`
`e ▸ hx` rewrites with `e : sᶜ = t` until the type of `hx` matches the stated type. `x ∉ s` and
`x ∈ sᶜ` are equal by definition, so `hx : x ∉ s` is accepted as `x ∈ sᶜ`. -/
example {α : Type} (s t : Set α) (e : sᶜ = t) (x : α) (hx : x ∉ s) (G : Prop) (k : x ∈ t → G) :
    G := by
  have hxt : x ∈ t := e ▸ hx
  exact k hxt

/-! ### R18. `obtain ⟨y, hy, rfl⟩ := hx` · context: `hx : x ∈ g '' s` → `y`, `hy : y ∈ s`; `x` → `g y`
`x ∈ g '' s` means `∃ y, y ∈ s ∧ g y = x`; the pattern `rfl` substitutes `x := g y`. -/
example {α β : Type} (g : β → α) (s : Set β) (x : α) (hx : x ∈ g '' s) (P : α → Prop)
    (h : ∀ y ∈ s, P (g y)) : P x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

/-! ### R19. `rw [leftInverse_invFun hg y]` · goal `P (invFun g (g y))` → `P y`
`Function.invFun g : α → β` (needs `[Nonempty β]`) picks some preimage of each point, by choice.
`Function.leftInverse_invFun : Injective g → LeftInverse (invFun g) g`, and `LeftInverse u g` means
`∀ y, u (g y) = y`, so `leftInverse_invFun hg y : invFun g (g y) = y`. -/
example {α β : Type} [Nonempty β] (g : β → α) (hg : Injective g) (y : β) (P : β → Prop)
    (h : P y) : P (invFun g (g y)) := by
  rw [leftInverse_invFun hg y]
  exact h

/-! ### R20. `intro a₁ a₂ h` on `Injective k` · goal → `a₁ = a₂` with `h : k a₁ = k a₂`
`Injective k` is by definition `∀ a₁ a₂, k a₁ = k a₂ → a₁ = a₂`; `intro` sees through it. -/
example {α β : Type} (k : α → β) (hk : ∀ a₁ a₂, k a₁ = k a₂ → a₁ = a₂) : Injective k := by
  intro a₁ a₂ h
  exact hk a₁ a₂ h

/-! ### R21. `by_cases hp : p` · goal list: one goal → two, with `hp : p` and `hp : ¬p`
For `p := x ∈ A`, the second hypothesis prints as `hp : x ∉ A`. -/
example (p G : Prop) (h1 : p → G) (h2 : ¬p → G) : G := by
  by_cases hp : p
  exact h1 hp
  exact h2 hp

/-! ### R22. `simp only [hp, if_true] at h` with `hp : p` · context: `if p then a else b` → `a` in `h`
`simp only [hp]` turns `p` into `True`; `if_true : (if True then a else b) = a`. -/
example {β : Type} (p : Prop) [Decidable p] (a b : β) (hp : p) (P : β → Prop)
    (h : P (if p then a else b)) : P a := by
  simp only [hp, if_true] at h
  exact h

/-! ### R23. `simp only [hp, if_false] at h` with `hp : ¬p` · context: `if p then a else b` → `b` in `h`
`simp only [hp]` turns `p` into `False`; `if_false : (if False then a else b) = b`. -/
example {β : Type} (p : Prop) [Decidable p] (a b : β) (hp : ¬p) (P : β → Prop)
    (h : P (if p then a else b)) : P b := by
  simp only [hp, if_false] at h
  exact h

/-! ### R24. `apply hf` with `hf : Injective f` · goal `a₁ = a₂` → `f a₁ = f a₂`
Equivalently `exact hf h` for `h : f a₁ = f a₂`. -/
example {α β : Type} (f : α → β) (hf : Injective f) (a₁ a₂ : α) (h : f a₁ = f a₂) : a₁ = a₂ := by
  apply hf
  exact h

/-! ### R25. `refine ⟨y, ?_, rfl⟩` · goal `g y ∈ g '' s` → `y ∈ s`
Membership in an image is an `∃ y, y ∈ s ∧ g y = x`, so it is built as `⟨y, hy, (proof of g y = x)⟩`. -/
example {α β : Type} (g : β → α) (s : Set β) (y : β) (hy : y ∈ s) : g y ∈ g '' s := by
  refine ⟨y, ?_, rfl⟩
  exact hy

/-! ### R26. `apply absurd ha` (`absurd : a → ¬a → b`) · goal `G` → `¬A`
From a proof `ha : A` and a refutation `¬A`, anything follows. -/
example (A G : Prop) (ha : A) (hna : ¬A) : G := by
  apply absurd ha
  exact hna

/-! ### R27. `intro b` on `Surjective k` · goal → `∃ a, k a = b`
`Surjective k` is by definition `∀ b, ∃ a, k a = b`. -/
example {α β : Type} (k : α → β) (hk : ∀ b, ∃ a, k a = b) : Surjective k := by
  intro b
  exact hk b

/-! ### R28. `rw [← Set.mem_compl_iff]` · goal `x ∉ s` → `x ∈ sᶜ`
`Set.mem_compl_iff : x ∈ sᶜ ↔ x ∉ s`. After it, `rw [e]` with `e : sᶜ = t` can reach the `sᶜ`. -/
example {α : Type} (s : Set α) (x : α) (h : x ∈ sᶜ) : x ∉ s := by
  rw [← Set.mem_compl_iff]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Through a complement, an image and a complement: R13 → R14 → R13 -/
example {α β : Type} (g : β → α) (s t : Set β) (hts : t ⊆ s) : (g '' tᶜ)ᶜ ⊆ (g '' sᶜ)ᶜ := by
  apply Set.compl_subset_compl.mpr
  apply Set.image_mono
  apply Set.compl_subset_compl.mpr
  exact hts

/-! ### W2. The intersection of all supersets of `s` is `s`: R5, R1, R2, R3 -/
example {α : Type} (s : Set α) : ⋂₀ {A | s ⊆ A} = s := by
  apply subset_antisymm
  · apply Set.sInter_subset_of_mem
    rw [Set.mem_setOf_eq]
  · apply Set.subset_sInter
    intro A hA
    exact hA

/-! ### W3. Inverting `g` on an image: R18 → R19 -/
example {α β : Type} [Nonempty β] (g : β → α) (hg : Injective g) (s : Set β) :
    ∀ x ∈ g '' s, invFun g x ∈ s := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [leftInverse_invFun hg y]
  exact hy

/-! ### W4. A piecewise function, case by case: R21, then R22/R23 on the goal -/
example {α β : Type} (A : Set α) [DecidablePred (· ∈ A)] (u v : α → β) (huv : ∀ x ∈ A, u x = v x) :
    ∀ x, (if x ∈ A then u x else v x) = v x := by
  intro x
  by_cases hx : x ∈ A
  · simp only [hx, if_true]
    exact huv x hx
  · simp only [hx, if_false]

end H040Guide

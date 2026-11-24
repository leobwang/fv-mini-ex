/- Guide for M059 (The kernel of a homomorphism).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the image of a hom, `a⁻¹ * b`).
Assumed: Lean basics.
-/
import Mathlib

namespace M059Guide

/-! # Part R · Reference entries -/

/-! ## Building a subgroup -/

/-! ### R1. `refine { carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }` · goal `Subgroup G` → three goals
A `Subgroup G` is a structure: a set `carrier` plus three closure proofs. In a `def` you can write the
same braces as a term, with `by …` (or a term) in place of each `?_`. The goals come out in the order
`mul_mem'`, `one_mem'`, `inv_mem'` (`mul_mem'` belongs to the innermost parent structure).
`exacts [e₁, e₂, e₃]` runs `exact eᵢ` on the open goals in order. -/
example {G : Type} [Group G] (S : Set G) (h1 : (1 : G) ∈ S)
    (hm : ∀ {a b : G}, a ∈ S → b ∈ S → a * b ∈ S) (hi : ∀ {x : G}, x ∈ S → x⁻¹ ∈ S) :
    Subgroup G := by
  refine { carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }
  exacts [hm, h1, hi]

/-! ### R2. Membership in `{x | P x}` is `P` itself (by definition) · `exact h` closes the goal -/
example {α : Type} (P : α → Prop) (a : α) (h : P a) : a ∈ {x | P x} := by
  exact h

/-! ### R3. `map_one` · `f 1 = 1` for a hom `f : G →* H` · goal -/
example {G H : Type} [Group G] [Group H] (f : G →* H) (P : H → Prop) (h : P 1) : P (f 1) := by
  rw [map_one]
  exact h

/-! ### R4. `intro a b ha hb` on implicit binders `∀ {a b : G}, …` · context gains `a b ha hb` -/
example {G : Type} (S : Set G) (Q : G → G → Prop) (h : ∀ a b, a ∈ S → b ∈ S → Q a b) :
    ∀ {a b : G}, a ∈ S → b ∈ S → Q a b := by
  intro a b ha hb
  exact h a b ha hb

/-! ### R5. `simp only [Set.mem_setOf_eq] at *` · context and goal: `a ∈ {x | P x}` → `P a` everywhere -/
example {α : Type} (P Q : α → Prop) (a : α) (ha : a ∈ {x | P x}) (h : P a → Q a) :
    a ∈ {x | Q x} := by
  simp only [Set.mem_setOf_eq] at *
  exact h ha

/-! ## Moving a hom past `*`, `⁻¹`, `1` -/

/-! ### R6. `map_mul` · `f (a * b) = f a * f b` · goal -/
example {G H : Type} [Group G] [Group H] (f : G →* H) (a b : G) (P : H → Prop)
    (h : P (f a * f b)) : P (f (a * b)) := by
  rw [map_mul]
  exact h

/-! ### R7. `one_mul` · `1 * a = a` · goal -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ### R8. `map_inv` · `f a⁻¹ = (f a)⁻¹` · goal -/
example {G H : Type} [Group G] [Group H] (f : G →* H) (a : G) (P : H → Prop)
    (h : P (f a)⁻¹) : P (f a⁻¹) := by
  rw [map_inv]
  exact h

/-! ### R9. `inv_one` · `1⁻¹ = 1` · goal -/
example {G : Type} [Group G] (P : G → Prop) (h : P 1) : P (1 : G)⁻¹ := by
  rw [inv_one]
  exact h

/-! ## Membership by definition -/

/-! ### R10. `Iff.rfl` · closes `A ↔ B` when `B` is `A` after unfolding definitions -/
example {α : Type} (P : α → Prop) (a : α) : a ∈ {x | P x} ↔ P a := by
  exact Iff.rfl

/-! ## Injectivity -/

/-! ### R11. `constructor` on `A ↔ B` · goal list: one goal → `A → B` (case `mp`), `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exacts [hab, hba]

/-! ### R12. `intro g hg` on `∀ g ∈ S, Q g` (which means `∀ g, g ∈ S → Q g`) · context gains `g`, `hg` -/
example {G : Type} (S : Set G) (Q : G → Prop) (h : ∀ g, g ∈ S → Q g) : ∀ g ∈ S, Q g := by
  intro g hg
  exact h g hg

/-! ### R13. `hiff.mp ha` (`Iff.mp`) · term: from `hiff : A ↔ B` and `ha : A`, a proof of `B` -/
example (A B : Prop) (hiff : A ↔ B) (ha : A) : B := by
  have hb : B := hiff.mp ha
  exact hb

/-! ### R14. `h₁.trans h₂.symm` (`Eq.trans`, `Eq.symm`) · term: `a = b`, `c = b` give `a = c` -/
example {α : Type} (a b c : α) (h₁ : a = b) (h₂ : c = b) : a = c := by
  have h : a = c := h₁.trans h₂.symm
  exact h

/-! ### R15. `hf h` for `hf : Function.Injective f` · term: `h : f a = f b` gives `a = b`
`a` and `b` are implicit: Lean reads them off `h`. -/
example {G H : Type} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f) (a b : G)
    (h : f a = f b) : a = b := by
  exact hf h

/-! ### R16. `intro a b hab` on `Function.Injective f` · context gains `a b`, `hab : f a = f b`
`Function.Injective f` is defined as `∀ ⦃a b⦄, f a = f b → a = b`; `intro` unfolds it. -/
example {G H : Type} [Group G] [Group H] (f : G →* H) (h : ∀ a b, f a = f b → a = b) :
    Function.Injective f := by
  intro a b hab
  exact h a b hab

/-! ### R17. `rw [hiff]` with `hiff : A ↔ B` · goal: the proposition `A` → `B` -/
example (A B : Prop) (P : Prop → Prop) (hiff : A ↔ B) (h : P B) : P A := by
  rw [hiff]
  exact h

/-! ### R18. `mul_inv_cancel` · `a * a⁻¹ = 1` · goal -/
example {G : Type} [Group G] (a : G) (P : G → Prop) (h : P 1) : P (a * a⁻¹) := by
  rw [mul_inv_cancel]
  exact h

/-! ### R19. `mul_inv_eq_one` · `a * b⁻¹ = 1 ↔ a = b`; `.mp` turns `h : a * b⁻¹ = 1` into `a = b` -/
example {G : Type} [Group G] (a b : G) (h : a * b⁻¹ = 1) : a = b := by
  exact mul_inv_eq_one.mp h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The image `{y | ∃ x, f x = y}` of a hom as a `Subgroup H`: R1, R4, R6, R8 -/
def img {G H : Type} [Group G] [Group H] (f : G →* H) : Subgroup H :=
  { carrier := {y | ∃ x, f x = y}
    one_mem' := ⟨1, map_one f⟩
    mul_mem' := by
      intro y z hy hz
      obtain ⟨x, hx⟩ := hy
      obtain ⟨w, hw⟩ := hz
      exact ⟨x * w, by rw [map_mul, hx, hw]⟩
    inv_mem' := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x⁻¹, by rw [map_inv, hx]⟩ }

/-! ### W2. Membership in a structure-built subgroup unfolds to its carrier: R10 -/
example {G H : Type} [Group G] [Group H] (f : G →* H) (y : H) : y ∈ img f ↔ ∃ x, f x = y :=
  Iff.rfl

/-! ### W3. `f a = f b` makes `f (a⁻¹ * b) = 1`: R6, R8, `rw [hab]`, then `inv_mul_cancel : a⁻¹ * a = 1` -/
example {G H : Type} [Group G] [Group H] (f : G →* H) (a b : G) (hab : f a = f b) :
    f (a⁻¹ * b) = 1 := by
  rw [map_mul]
  rw [map_inv]
  rw [hab]
  rw [inv_mul_cancel]

end M059Guide

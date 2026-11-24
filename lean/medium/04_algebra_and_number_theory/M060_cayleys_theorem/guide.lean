/- Guide for M060 (Cayley's theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (shifts `x ↦ x + k` of `ℤ`).
Assumed: Lean basics.
-/
import Mathlib

namespace M060Guide

/-! # Part R · Reference entries -/

/-! ## Building the two structures -/

/-! ### R1. `refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }` · goal `Equiv.Perm α` → two goals
`Equiv.Perm α` is `α ≃ α`: a function with a two-sided inverse. The two `?_` are the inverse laws. -/
example {α : Type} (f g : α → α) (hl : ∀ x, g (f x) = x) (hr : ∀ x, f (g x) = x) :
    Equiv.Perm α := by
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  exacts [hl, hr]

/-! ### R2. `intro x` on `Function.LeftInverse g f` · context gains `x`; goal `g (f x) = x`
`Function.LeftInverse g f` is by definition `∀ x, g (f x) = x`; `Function.RightInverse g f` is
`∀ x, f (g x) = x`. `intro` sees through the definition. When `f`, `g` are written as `fun x => …`,
the new goal keeps the applications `(fun x => …) a` unreduced: `rw` cannot see inside them, but
`exact` (which compares up to unfolding) and `simp` can. -/
example {α : Type} (f g : α → α) (hl : ∀ x, g (f x) = x) :
    Function.LeftInverse (fun x => g x) (fun x => f x) := by
  intro x
  exact hl x

/-! ### R3. `inv_mul_cancel_left` · `a⁻¹ * (a * b) = b` · goal -/
example {G : Type} [Group G] (a b : G) (P : G → Prop) (h : P b) : P (a⁻¹ * (a * b)) := by
  rw [inv_mul_cancel_left]
  exact h

/-! ### R4. `mul_inv_cancel_left` · `a * (a⁻¹ * b) = b` · goal -/
example {G : Type} [Group G] (a b : G) (P : G → Prop) (h : P b) : P (a * (a⁻¹ * b)) := by
  rw [mul_inv_cancel_left]
  exact h

/-! ### R5. `refine { toFun := φ, map_one' := ?_, map_mul' := ?_ }` · goal `M →* N` → two goals
`M →* N` is a monoid homomorphism: a function with `φ 1 = 1` and `φ (x * y) = φ x * φ y`. -/
example {M N : Type} [Monoid M] [Monoid N] (φ : M → N) (h1 : φ 1 = 1)
    (hm : ∀ a b, φ (a * b) = φ a * φ b) : M →* N := by
  refine { toFun := φ, map_one' := ?_, map_mul' := ?_ }
  exacts [h1, hm]

/-! ## Equations between permutations -/

/-! ### R6. `ext x` (lemma `Equiv.ext`) · goal `σ = τ` → context gains `x`, goal `σ x = τ x` -/
example {α : Type} (σ τ : Equiv.Perm α) (h : ∀ x, σ x = τ x) : σ = τ := by
  ext x
  exact h x

/-! ### R7. `Equiv.coe_fn_mk` · goal: a hand-built permutation applied to `x` → `f x` -/
example {α : Type} (f g : α → α) (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f)
    (x : α) (P : α → Prop) (h : P (f x)) :
    P (({ toFun := f, invFun := g, left_inv := hl, right_inv := hr } : Equiv.Perm α) x) := by
  rw [Equiv.coe_fn_mk]
  exact h

/-! ### R8. `Equiv.Perm.one_apply` · goal: `1 x` → `x` (`1` is the identity permutation) -/
example {α : Type} (x : α) (P : α → Prop) (h : P x) : P ((1 : Equiv.Perm α) x) := by
  rw [Equiv.Perm.one_apply]
  exact h

/-! ### R9. `one_mul` · `1 * a = a` · goal -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ### R10. `Equiv.Perm.mul_apply` · goal: `(σ * τ) x` → `σ (τ x)` (`*` is composition) -/
example {α : Type} (σ τ : Equiv.Perm α) (x : α) (P : α → Prop) (h : P (σ (τ x))) :
    P ((σ * τ) x) := by
  rw [Equiv.Perm.mul_apply]
  exact h

/-! ### R11. `mul_assoc` · `a * b * c = a * (b * c)` · goal -/
example {M : Type} [Monoid M] (a b c : M) (P : M → Prop) (h : P (a * (b * c))) :
    P (a * b * c) := by
  rw [mul_assoc]
  exact h

/-! ### R12. `rfl` · closes "a hand-built map, applied" `= its formula`: both sides unfold to the same term -/
example {M α : Type} [Monoid M] (φ : M → Equiv.Perm α) (h1 : φ 1 = 1)
    (hm : ∀ a b, φ (a * b) = φ a * φ b) (a : M) (x : α) :
    ({ toFun := φ, map_one' := h1, map_mul' := hm } : M →* Equiv.Perm α) a x = φ a x := by
  rfl

/-! ## Injectivity -/

/-! ### R13. `intro a b h` on `Function.Injective f` · context gains `a b` and `h : f a = f b`; goal `a = b` -/
example {α β : Type} (f : α → β) (k : ∀ a b, f a = f b → a = b) : Function.Injective f := by
  intro a b h
  exact k a b h

/-! ### R14. `have := congrArg (fun σ => σ x) h` · context gains `this : σ x = τ x` from `h : σ = τ` -/
example {α : Type} (σ τ : Equiv.Perm α) (x : α) (h : σ = τ) (Q : Prop) (k : σ x = τ x → Q) : Q := by
  have := congrArg (fun σ : Equiv.Perm α => σ x) h
  exact k this

/-! ### R15. `mul_one` · `a * 1 = a` · goal -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R16. `simpa [l] using this` · closes the goal: simplify `this` and the goal with `l`, then match -/
example {α : Type} (f : α → α) (l : ∀ x, f x = x) (a b : α) (this : f a = f b) : a = b := by
  simpa [l] using this

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- The shift `x ↦ x + k` of `ℤ`, built with R1. -/
def shift (k : ℤ) : Equiv.Perm ℤ :=
  { toFun := fun x => x + k
    invFun := fun x => x - k
    left_inv := fun x => by simp
    right_inv := fun x => by simp }

/-! ### W1. A formula for the applied permutation is `rfl` (R12) -/
example (k x : ℤ) : shift k x = x + k := rfl

/-! ### W2. An equation of permutations: R6, then `simp` (R7, R8) -/
example : shift 0 = 1 := by
  ext x
  simp [shift]

/-! ### W3. A product of permutations: R6, then `simp` (R7, R10), then `ring` for what is left -/
example (a b : ℤ) : shift (a + b) = shift a * shift b := by
  ext x
  simp [shift]
  ring

/-! ### W4. Injectivity by evaluating at one point: R13, R14, R16 -/
example : Function.Injective shift := by
  intro a b h
  have := congrArg (fun σ : Equiv.Perm ℤ => σ 0) h
  simpa [shift] using this

end M060Guide

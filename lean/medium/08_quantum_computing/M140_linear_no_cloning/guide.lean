/- Guide for M140 (Linear no-cloning).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`Fin 2`, `Fin 3`, real vectors).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix

namespace M140Guide

/-! # Part R · Reference entries -/

/-! ## Proof by contradiction and two distinct indices -/

/-! ### R1. `intro h` on `¬ A` · goal `¬ A` → context gains `h : A`, goal `False`
`¬ A` is defined as `A → False`, so `intro` works on it like on an implication. -/
example (A : Prop) (g : A → False) : ¬ A := by
  intro h
  exact g h

/-! ### R2. `obtain ⟨i, j, hij⟩ := exists_pair_ne α` · context gains `i j : α` and `hij : i ≠ j`
`exists_pair_ne α : ∃ x y, x ≠ y` needs `[Nontrivial α]`: "α has at least two elements". -/
example (α : Type) [Nontrivial α] (G : Prop) (g : ∀ x y : α, x ≠ y → G) : G := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne α
  exact g i j hij

/-! ## Showing a vector is nonzero -/

/-! ### R3. `intro hk` on `a ≠ b` · goal `a ≠ b` → context gains `hk : a = b`, goal `False`
`a ≠ b` is `a = b → False`. As a term: `fun hk => by …`. -/
example {α : Type} (a b : α) (g : a = b → False) : a ≠ b := by
  intro hk
  exact g hk

/-! ### R4. `have := congrFun hk x` · context gains `this : f x = g x`
`congrFun : f = g → ∀ x, f x = g x` evaluates an equation of functions (vectors) at one index. -/
example {ι β : Type} (f g : ι → β) (hk : f = g) (x : ι) (G : Prop) (k : f x = g x → G) : G := by
  have := congrFun hk x
  exact k this

/-! ### R5. `Pi.single_eq_same` · `Pi.single i x i = x` · goal: the basis vector at its own index
`Pi.single i x : ι → α` is the vector with `x` at index `i` and `0` elsewhere. -/
example {ι α : Type} [DecidableEq ι] [Zero α] (i : ι) (x : α) (P : α → Prop) (h : P x) :
    P ((Pi.single i x : ι → α) i) := by
  rw [Pi.single_eq_same]
  exact h

/-! ### R6. `Pi.zero_apply` · `(0 : ι → α) k = 0` · goal: the zero vector at an index -/
example {ι α : Type} [Zero α] (k : ι) (P : α → Prop) (h : P 0) : P ((0 : ι → α) k) := by
  rw [Pi.zero_apply]
  exact h

/-! ### R7. `simp at h` turning `h` into `False` · goal list: the goal is closed
`simp` knows `one_ne_zero : 1 ≠ 0`, so `h : 1 = 0` simplifies to `False`, which proves anything. -/
example (G : Prop) (h : (1 : ℂ) = 0) : G := by
  simp at h

/-! ## Using the cloner -/

/-! ### R8. `obtain ⟨c, -, hc⟩ := h a ha` · context gains a witness and the facts you keep
`h a ha` applies `h : ∀ x, Q x → ∃ y, R x y ∧ S x y`; `obtain` unpacks `∃` and `∧`; `-` drops a part. -/
example {α β : Type} (Q : α → Prop) (R S : α → β → Prop) (h : ∀ x, Q x → ∃ y, R x y ∧ S x y)
    (a : α) (ha : Q a) (G : Prop) (g : ∀ y, S a y → G) : G := by
  obtain ⟨b, -, hb⟩ := h a ha
  exact g b hb

/-! ## A superposition is nonzero -/

/-! ### R9. `Pi.add_apply` · `(f + g) x = f x + g x` · goal: a sum of vectors at an index -/
example {ι α : Type} [Add α] (f g : ι → α) (x : ι) (P : α → Prop) (h : P (f x + g x)) :
    P ((f + g) x) := by
  rw [Pi.add_apply]
  exact h

/-! ### R10. `Pi.single_eq_of_ne` · `i' ≠ i → Pi.single i x i' = 0` · goal: a basis vector off its index -/
example {ι α : Type} [DecidableEq ι] [Zero α] (i i' : ι) (hne : i' ≠ i) (x : α) (P : α → Prop)
    (h : P 0) : P ((Pi.single i x : ι → α) i') := by
  rw [Pi.single_eq_of_ne hne]
  exact h

/-! ### R11. `Ne.symm` (written `hab.symm`) · `a ≠ b → b ≠ a` · context gains the flipped fact -/
example {α : Type} (a b : α) (hab : a ≠ b) (G : Prop) (g : b ≠ a → G) : G := by
  have hba := hab.symm
  exact g hba

/-! ## Splitting the superposition -/

/-! ### R12. `funext p` · goal `f = g` (functions) → context gains `p`, goal `f p = g p` -/
example {ι β : Type} (f g : ι → β) (h : ∀ p, f p = g p) : f = g := by
  funext p
  exact h p

/-! ### R13. `add_mul` · `(a + b) * c = a * c + b * c` · goal: distribute on the right -/
example {α : Type} [Semiring α] (a b c : α) (P : α → Prop) (h : P (a * c + b * c)) :
    P ((a + b) * c) := by
  rw [add_mul]
  exact h

/-! ### R14. `rw [e] at h` · context: hypothesis `h` rewritten; goal unchanged -/
example {α : Type} (a b : α) (P : α → Prop) (e : a = b) (h : P a) : P b := by
  rw [e] at h
  exact h

/-! ### R15. `Matrix.mulVec_add` · `A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y` · goal: linearity of `A *ᵥ`
`A *ᵥ x` is `Matrix.mulVec A x`, the matrix `A : Matrix m n α` times the column vector `x : n → α`. -/
example {m n α : Type} [Fintype n] [Semiring α] (A : Matrix m n α) (x y : n → α)
    (P : (m → α) → Prop) (h : P (A *ᵥ x + A *ᵥ y)) : P (A *ᵥ (x + y)) := by
  rw [Matrix.mulVec_add]
  exact h

/-! ## Evaluating at one index pair -/

/-! ### R16. `Pi.smul_apply`, then `smul_eq_mul` · goal: `(c • f) x` → `c • f x` → `c * f x` -/
example {ι α : Type} [Mul α] (c : α) (f : ι → α) (x : ι) (P : α → Prop) (h : P (c * f x)) :
    P ((c • f) x) := by
  rw [Pi.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R17. `Pi.single_apply` · `Pi.single i x i' = if i' = i then x else 0` · goal: basis vector → `if` -/
example {ι α : Type} [DecidableEq ι] [Zero α] (i i' : ι) (x : α) (P : α → Prop)
    (h : P (if i' = i then x else 0)) : P ((Pi.single i x : ι → α) i') := by
  rw [Pi.single_apply]
  exact h

/-! ### R18. `simp [hne]` with `hne : a ≠ b` · goal: decides each `if` on `a = b` or `a = a`
`a = a` simplifies to `True` by itself; `a = b` needs `hne`. -/
example {ι α : Type} [DecidableEq ι] (a b : ι) (hne : a ≠ b) (x y : α) (P : α → Prop)
    (h : P y ∧ P x) : P (if a = b then x else y) ∧ P (if a = a then x else y) := by
  simp [hne]
  exact h

/-! ### R19. `exact hc h.symm` · closes `False` from `hc : a ≠ b` and `h : b = a`
`h.symm : a = b` (`Eq.symm`), and `hc` is a function `a = b → False`. -/
example {α : Type} (a b : α) (hc : a ≠ b) (h : b = a) : False := by
  exact hc h.symm

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A basis vector of `ℝ^3` is nonzero: R3, R4, then `simp` (R5, R6, R7) -/
example : (Pi.single (2 : Fin 3) (5 : ℝ) : Fin 3 → ℝ) ≠ 0 := by
  intro hk
  have := congrFun hk 2
  simp at this

/-! ### W2. Splitting the SECOND slot of a product vector: R12, then `simp [mul_add]` (R9) -/
example (u w e : Fin 2 → ℝ) :
    (fun p : Fin 2 × Fin 2 => e p.1 * (u + w) p.2) =
      (fun p => e p.1 * u p.2) + (fun p => e p.1 * w p.2) := by
  funext p
  simp [mul_add]

/-! ### W3. A matrix fixing both basis vectors of `ℝ^2` cannot kill their sum: R14, R15, R4, `simp` -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (hx : A *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (hy : A *ᵥ Pi.single 1 1 = Pi.single 1 1)
    (h : A *ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0) : False := by
  rw [Matrix.mulVec_add, hx, hy] at h
  have := congrFun h 0
  simp at this

/-! ### W4. A scaled product vector `a • (|0⟩ ⊗ |0⟩)` vanishes off the diagonal: R16, R17, R18 -/
example (a c : ℂ)
    (h : (a • fun p : Fin 3 × Fin 3 => (Pi.single 0 1 : Fin 3 → ℂ) p.1 * (Pi.single 0 1 : Fin 3 → ℂ) p.2) (0, 2) = c) :
    c = 0 := by
  simp [Pi.single_apply] at h
  exact h.symm

end M140Guide

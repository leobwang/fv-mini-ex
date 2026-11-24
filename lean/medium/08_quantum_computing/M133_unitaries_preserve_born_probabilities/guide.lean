/- Guide for M133 (Unitaries preserve Born probabilities).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (columns instead of rows, two
complex numbers instead of a vector).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.Operators.Unitary

open scoped Matrix

namespace M133Guide

/-! # Part R · Reference entries -/

/-! ## Moving `U` through a dot product (vector–matrix algebra) -/

/-! ### R1. `Matrix.star_mulVec` · goal: `star (M *ᵥ v)` → `star v ᵥ* Mᴴ`
The conjugate of a column `M v` is the row `v̄` times the conjugate transpose `Mᴴ`. -/
example {m n α : Type} [Fintype n] [NonUnitalSemiring α] [StarRing α] (M : Matrix m n α)
    (v : n → α) (P : (m → α) → Prop) (h : P (star v ᵥ* Mᴴ)) : P (star (M *ᵥ v)) := by
  rw [Matrix.star_mulVec]
  exact h

/-! ### R2. `Matrix.dotProduct_mulVec` · goal: `v ⬝ᵥ A *ᵥ w` → `v ᵥ* A ⬝ᵥ w`
Move the matrix from the right factor of a dot product to the left one: `vᵀ(Aw) = (vᵀA)w`. -/
example {m n α : Type} [Fintype m] [Fintype n] [NonUnitalSemiring α] (v : m → α)
    (A : Matrix m n α) (w : n → α) (P : α → Prop) (h : P (v ᵥ* A ⬝ᵥ w)) : P (v ⬝ᵥ A *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec]
  exact h

/-! ### R3. `Matrix.vecMul_vecMul` · goal: two row–matrix products → one product with `M * N` -/
example {m n o α : Type} [Fintype m] [Fintype n] [NonUnitalSemiring α] (v : m → α)
    (M : Matrix m n α) (N : Matrix n o α) (P : (o → α) → Prop) (h : P (v ᵥ* (M * N))) :
    P (v ᵥ* M ᵥ* N) := by
  rw [Matrix.vecMul_vecMul]
  exact h

/-! ### R4. `Matrix.star_eq_conjTranspose`, right to left · goal: `Mᴴ` → `star M`
The unitary lemma R5 is stated with `star`, so turn `ᴴ` back into `star` first. -/
example {n α : Type} [Star α] (M : Matrix n n α) (P : Matrix n n α → Prop) (h : P (star M)) :
    P Mᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact h

/-! ### R5. `Matrix.UnitaryGroup.star_mul_self` · goal: `star ↑U * ↑U` → `1`
`U : 𝐔[n]` is a unitary bundled with its proof; `U.val` (printed `↑U`) is the bare matrix. -/
example {n : Type} [Fintype n] [DecidableEq n] (U : 𝐔[n]) (P : Matrix n n ℂ → Prop) (h : P 1) :
    P (star U.val * U.val) := by
  rw [Matrix.UnitaryGroup.star_mul_self]
  exact h

/-! ### R6. `Matrix.vecMul_one` · goal: `v ᵥ* 1` → `v` -/
example {n α : Type} [Fintype n] [DecidableEq n] [NonAssocSemiring α] (v : n → α)
    (P : (n → α) → Prop) (h : P v) : P (v ᵥ* 1) := by
  rw [Matrix.vecMul_one]
  exact h

/-! ## From `star v ⬝ᵥ v : ℂ` to `∑ ‖vᵢ‖² : ℝ` -/

/-! ### R7. `intro v` · goal `∀ v, Q v` → context gains `v`, goal `Q v` -/
example {n : Type} (Q : (n → ℂ) → Prop) (h : ∀ w, Q w) : ∀ v : n → ℂ, Q v := by
  intro v
  exact h v

/-! ### R8. `dotProduct` (unfold) · goal: `v ⬝ᵥ w` → `∑ i, v i * w i` -/
example {n α : Type} [Fintype n] [Mul α] [AddCommMonoid α] (v w : n → α) (P : α → Prop)
    (h : P (∑ i, v i * w i)) : P (v ⬝ᵥ w) := by
  simp only [dotProduct]
  exact h

/-! ### R9. `Pi.star_apply` · goal: `star v i` (entry of the conjugated vector) → `star (v i)` -/
example {n : Type} (v : n → ℂ) (i : n) (P : ℂ → Prop) (h : P (star (v i))) : P (star v i) := by
  rw [Pi.star_apply]
  exact h

/-! ### R10. `Complex.star_def` · goal: `star z` → `(starRingEnd ℂ) z`, Mathlib's `conj z` -/
example (z : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z)) : P (star z) := by
  simp only [Complex.star_def]
  exact h

/-! ### R11. `Complex.conj_mul'` · goal: `conj z * z` → `↑‖z‖ ^ 2` (the real `‖z‖` cast to `ℂ`) -/
example (z : ℂ) (P : ℂ → Prop) (h : P (↑‖z‖ ^ 2)) : P ((starRingEnd ℂ) z * z) := by
  rw [Complex.conj_mul']
  exact h

/-! ### R12. `Complex.ofReal_sum` · goal: cast of a real sum → sum of casts -/
example {n : Type} [Fintype n] (f : n → ℝ) (P : ℂ → Prop) (h : P (∑ i, (f i : ℂ))) :
    P ((∑ i, f i : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact h

/-! ### R13. `Complex.ofReal_pow` · goal: cast of a power → power of the cast -/
example (r : ℝ) (k : ℕ) (P : ℂ → Prop) (h : P ((r : ℂ) ^ k)) : P ((r ^ k : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow]
  exact h

/-! ## Chaining the milestones and leaving `ℂ` -/

/-! ### R14. `Eq.trans`, `Eq.symm` · context gains `h : a = d` from a chain of equations
`h₁.trans h₂ : a = c` glues `a = b` and `b = c`; `h₃.symm : c = d` flips `d = c`. -/
example {α : Type} (a b c d : α) (h₁ : a = b) (h₂ : b = c) (h₃ : d = c) : a = d := by
  have h := h₁.trans (h₂.trans h₃.symm)
  exact h

/-! ### R15. `rw [φ.normalized'] at h` (`Ket.normalized'`) · context: `h` rewritten, goal unchanged
`φ.normalized' : ∑ x, ‖φ.vec x‖ ^ 2 = 1` is the proof field stored in every `Ket`. -/
example {n : Type} [Fintype n] (φ : Ket n) (P : ℝ → Prop) (h : P (∑ x, ‖φ.vec x‖ ^ 2)) : P 1 := by
  rw [φ.normalized'] at h
  exact h

/-! ### R16. `exact_mod_cast h` · closes `x = y` in `ℝ` from `h : ↑x = ↑y` in `ℂ` -/
example (x y : ℝ) (h : (x : ℂ) = (y : ℂ)) : x = y := by
  exact_mod_cast h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The column-vector version of R3–R6: `star U` undoes `U` on a column -/
example {n : Type} [Fintype n] [DecidableEq n] (U : 𝐔[n]) (v : n → ℂ) :
    star U.val *ᵥ (U.val *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.UnitaryGroup.star_mul_self]
  rw [Matrix.one_mulVec]

/-! ### W2. `simp` does R9–R13 by itself: two complex numbers instead of a vector -/
example (a b : ℂ) : ((‖a‖ ^ 2 + ‖b‖ ^ 2 : ℝ) : ℂ) = star a * a + star b * b := by
  simp [Complex.conj_mul']

/-! ### W3. Leaving `ℂ`: a chain R14, a rewrite in a hypothesis, then a cast -/
example (x y : ℝ) (c : ℂ) (h₁ : (x : ℂ) = c) (h₂ : (y : ℂ) = c) (hy : y = 2) : x = 2 := by
  have h := h₁.trans h₂.symm
  rw [hy] at h
  exact_mod_cast h

end M133Guide

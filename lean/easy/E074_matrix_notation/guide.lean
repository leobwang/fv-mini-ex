/- Guide for E074 (Matrix notation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other matrices and vectors).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix

namespace E074Guide

/-! # Part R · Reference entries -/

/-! ## Reading one entry -/

/-! ### R1. `rfl` · closes `!![a, b; c, d] i j = x` when `x` is that entry
`!![a, b; c, d]` is the matrix with rows `a b` and `c d`; `M i j` is row `i`, column `j`, from 0.
Lean computes an entry of a literal by unfolding, so `rfl` closes the goal. -/
example {α : Type} (a b c d : α) : !![a, b; c, d] 1 0 = c := by
  rfl

/-! ### R2. Unfold a definition: `simp only [D]` · goal: the name `D` → its body -/
def D : Matrix (Fin 2) (Fin 2) ℝ := !![5, 6; 7, 8]
example (P : Matrix (Fin 2) (Fin 2) ℝ → Prop) (h : P !![5, 6; 7, 8]) : P D := by
  simp only [D]
  exact h

/-! ## Determinant -/

/-! ### R3. `Matrix.det_fin_two` · goal: `M.det` → `M 0 0 * M 1 1 - M 0 1 * M 1 0` -/
example {R : Type} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (P : R → Prop)
    (h : P (M 0 0 * M 1 1 - M 0 1 * M 1 0)) : P M.det := by
  rw [Matrix.det_fin_two]
  exact h

/-! ### R4. Entry of a literal inside a goal: `simp` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P b) : P (!![a, b; c, d] 0 1) := by
  simp
  exact h

/-! ### R5. `norm_num` · closes a goal made only of numerals -/
example : (5 : ℝ) * 8 - 6 * 7 = -2 := by
  norm_num

/-! ## Matrix and vector equations → entries -/

/-! ### R6. `ext i j` (lemma `Matrix.ext`) · goal `M = N` → context gains `i j`, goal is one entry -/
example {α : Type} (M N : Matrix (Fin 2) (Fin 2) α) (h : ∀ i j, M i j = N i j) : M = N := by
  ext i j
  exact h i j

/-! ### R7. `fin_cases i` · context loses `i : Fin 2`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`. -/
example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  fin_cases i
  exacts [h0, h1]

/-! ### R8. `Matrix.transpose_apply` · goal: entry `(i, j)` of `Mᵀ` → entry `(j, i)` of `M`
`rfl` uses this fact by itself, which is why it can close entries of a transpose. -/
example {α : Type} (M : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2) (P : α → Prop) (h : P (M j i)) :
    P (Mᵀ i j) := by
  rw [Matrix.transpose_apply]
  exact h

/-! ### R9. `ext i` (lemma `funext`) · goal `v = w` for vectors `Fin 2 → α` → one entry -/
example {α : Type} (v w : Fin 2 → α) (h : ∀ i, v i = w i) : v = w := by
  ext i
  exact h i

/-! ## Matrix times vector -/

/-! ### R10. `Matrix.mulVec` · goal: `(M *ᵥ v) i` → the dot product of row `i` of `M` with `v` -/
example {α : Type} [NonUnitalNonAssocSemiring α] (M : Matrix (Fin 2) (Fin 2) α) (v : Fin 2 → α)
    (i : Fin 2) (P : α → Prop) (h : P ((fun j => M i j) ⬝ᵥ v)) : P ((M *ᵥ v) i) := by
  simp only [Matrix.mulVec]
  exact h

/-! ### R11. `dotProduct` · goal: `v ⬝ᵥ w` → `∑ i, v i * w i` -/
example {α : Type} [Mul α] [AddCommMonoid α] (v w : Fin 2 → α) (P : α → Prop)
    (h : P (∑ i, v i * w i)) : P (v ⬝ᵥ w) := by
  simp only [dotProduct]
  exact h

/-! ### R12. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R13. Entry of a vector literal `![a, b] i`: `simp` (`Matrix.cons_val_…`) · goal -/
example {α : Type} (a b : α) (P : α → Prop) (h : P b) : P (![a, b] 1) := by
  simp
  exact h

/-! ## Matrix times matrix, scalars, identity -/

/-! ### R14. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R15. `Matrix.smul_apply`, `smul_eq_mul` · goal: entry of `c • M` → `c * (entry of M)` -/
example {α : Type} [Mul α] (c : α) (M : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2) (P : α → Prop)
    (h : P (c * M i j)) : P ((c • M) i j) := by
  rw [Matrix.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R16. `Matrix.one_apply_eq`, `Matrix.one_apply_ne` · goal: entries of the identity `1` -/
example (P : ℝ → Prop) (h1 : P 1) (h0 : P 0) :
    P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ∧ P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1) := by
  simp
  exact ⟨h1, h0⟩

/-! ### R17. `ring` · closes an identity of commutative rings with variables -/
example (x y z w : ℝ) : x * w + y * -z = x * w - y * z := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

def B : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 7, 5]

/-! ### W1. A determinant: R2, R3, R4 in one `simp`, then R5 -/
example : B.det = 3 := by
  simp [B, Matrix.det_fin_two]
  norm_num

/-! ### W2. A transpose, entry by entry: R6, R7, then R1 on each entry -/
example : Bᵀ = !![2, 7; 1, 5] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals rfl

/-! ### W3. Matrix times vector: R9, R7, then R10–R13 in one `simp`, then R5 -/
example : B *ᵥ ![1, 2] = ![4, 17] := by
  ext i
  fin_cases i
  all_goals simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals norm_num

/-! ### W4. A product with variables: R6, R7, then R14, R12 (with R4, R15, R16 automatic), then R17 -/
example (x y : ℝ) : !![x, 0; 0, y] * !![y, 0; 0, x] = (x * y) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

end E074Guide

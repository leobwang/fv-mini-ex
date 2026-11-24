/- Guide for E110 (The unitary group).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the phase gate `S`).
Assumed: Lean basics.
-/
import Mathlib

open Matrix Complex

namespace E110Guide

/-! # Part R · Reference entries -/

/-! ## Unitary membership → a matrix equation -/

/-! ### R1. `Matrix.mem_unitaryGroup_iff` · goal: membership → the equation `M * star M = 1` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M * star M = 1) : M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact h

/-! ### R2. `Matrix.star_eq_conjTranspose` · goal: `star M` → `Mᴴ` (conjugate transpose) -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P Mᴴ) :
    P (star M) := by
  rw [Matrix.star_eq_conjTranspose]
  exact h

/-! ## Matrix equations → entries -/

/-! ### R3. `ext i j` (lemma `Matrix.ext`) · goal `M = N` → context gains `i j`, goal is one entry -/
example {α : Type} (M N : Matrix (Fin 2) (Fin 2) α) (h : ∀ i j, M i j = N i j) : M = N := by
  ext i j
  exact h i j

/-! ### R4. `fin_cases i` · context loses `i : Fin 2`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`. -/
example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  fin_cases i
  exacts [h0, h1]

/-! ## Evaluating one entry (`simp` applies R5–R11 by itself once it is given the names) -/

/-! ### R5. Unfold a definition: `simp only [D]` · goal: the name `D` → its body -/
def D : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 4]
example (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P !![1, 2; 3, 4]) : P D := by
  simp only [D]
  exact h

/-! ### R6. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R7. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R8. `Matrix.conjTranspose_apply` · goal: entry `(i, j)` of `Mᴴ` → `star` of entry `(j, i)` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (P : ℂ → Prop) (h : P (star (M j i))) :
    P (Mᴴ i j) := by
  rw [Matrix.conjTranspose_apply]
  exact h

/-! ### R9. Entry of a literal `!![a, b; c, d] i j` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P b) : P (!![a, b; c, d] 0 1) := by
  simp
  exact h

/-! ### R10. `Matrix.one_apply_eq`, `Matrix.one_apply_ne` · goal: entries of the identity `1` -/
example (P : ℂ → Prop) (h1 : P 1) (h0 : P 0) :
    P ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∧ P ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  simp
  exact ⟨h1, h0⟩

/-! ### R11. `star_neg`, `star_one`, `star_zero` · goal: `star` of an integer numeral → the numeral
On `ℂ`, `star z` is the complex conjugate; a real number is its own conjugate. -/
example (P : ℂ → Prop) (h : P (-1)) : P (star (-1 : ℂ)) := by
  rw [star_neg, star_one]
  exact h

/-! ## Products of unitaries -/

/-! ### R12. `Submonoid.mul_mem` · `x ∈ S → y ∈ S → x * y ∈ S` · goal `x * y ∈ S` → two goals
`Matrix.unitaryGroup n ℂ` is a `Submonoid`, so this applies to it. As a term: `Submonoid.mul_mem _ hx hy`. -/
example {M : Type} [Monoid M] (S : Submonoid M) (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    x * y ∈ S := by
  apply Submonoid.mul_mem
  exacts [hx, hy]

/-! ## The other side: `star A * A = 1` -/

/-! ### R13. `rw [← Matrix.star_eq_conjTranspose]` · goal: `Mᴴ` → `star M` (R2 right to left) -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P (star M)) :
    P Mᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact h

/-! ### R14. `Matrix.mem_unitaryGroup_iff'` with `.mp` · context gains `star A * A = 1`
The lemma is `A ∈ unitaryGroup m α ↔ star A * A = 1`; `(e : P ↔ Q).mp : P → Q`. -/
example {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (hA : A ∈ Matrix.unitaryGroup m ℂ)
    (G : Prop) (g : star A * A = 1 → G) : G := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  exact g h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- The phase gate `S = diag(1, i)`. -/
def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, I]

/-! ### W1. Unitary by entries: R1, R2, then R3, R4, then `simp` with R5–R7 (R8–R11 automatic) -/
example : S ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### W2. Without R6, R7, `simp [S]` stops at `v ᵥ* Mᴴ` (a row vector times a matrix) -/
example : S * Sᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-! ### W3. Closure under products: R12 as a term, applied to two membership proofs -/
example (hS : S ∈ Matrix.unitaryGroup (Fin 2) ℂ) : S * S * S ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ hS hS) hS

end E110Guide

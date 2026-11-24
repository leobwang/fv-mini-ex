/- Guide for E111 (Kronecker products of gates).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (three-factor products, gates on
one part only, single entries).
The infoview never prints `A ⊗ₖ B`: it prints `kroneckerMap (fun x1 x2 => x1 * x2) A B`.
Assumed: Lean basics.
-/
import Mathlib

open Matrix
open scoped Kronecker

namespace E111Guide

/-! # Part R · Reference entries -/

/-! ## Products of Kronecker products -/

/-! ### R1. `rw [← Matrix.mul_kronecker_mul]` · goal: `(A ⊗ₖ B) * (C ⊗ₖ D)` → `(A * C) ⊗ₖ (B * D)`
The lemma (mixed-product rule) is `(A * C) ⊗ₖ (B * D) = A ⊗ₖ B * C ⊗ₖ D`; `←` uses it right to left.
One `rw` merges one product (the first it finds, and every identical copy of it). -/
example {α : Type} [CommSemiring α] {k l : Type} [Fintype k] [Fintype l]
    (A C : Matrix k k α) (B D : Matrix l l α) (P : Matrix (k × l) (k × l) α → Prop)
    (h : P ((A * C) ⊗ₖ (B * D))) : P ((A ⊗ₖ B) * (C ⊗ₖ D)) := by
  rw [← Matrix.mul_kronecker_mul]
  exact h

/-! ### R2. `rw [Matrix.one_kronecker_one]` · goal: `1 ⊗ₖ 1` → `1` (identity ⊗ identity = identity) -/
example {α : Type} [MulZeroOneClass α] {k l : Type} [DecidableEq k] [DecidableEq l]
    (P : Matrix (k × l) (k × l) α → Prop) (h : P 1) :
    P ((1 : Matrix k k α) ⊗ₖ (1 : Matrix l l α)) := by
  rw [Matrix.one_kronecker_one]
  exact h

/-! ## Identity factors -/

/-! ### R3. `rw [Matrix.mul_one]` · goal: `M * 1` → `M` -/
example {α : Type} [NonAssocSemiring α] {k : Type} [Fintype k] [DecidableEq k]
    (M : Matrix k k α) (P : Matrix k k α → Prop) (h : P M) : P (M * 1) := by
  rw [Matrix.mul_one]
  exact h

/-! ### R4. `rw [Matrix.one_mul]` · goal: `1 * M` → `M` -/
example {α : Type} [NonAssocSemiring α] {k : Type} [Fintype k] [DecidableEq k]
    (M : Matrix k k α) (P : Matrix k k α → Prop) (h : P M) : P (1 * M) := by
  rw [Matrix.one_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Three Kronecker products: R1 twice, each call merges the innermost product it finds -/
example {k l : Type} [Fintype k] [Fintype l] (A C E : Matrix k k ℂ) (B D F : Matrix l l ℂ) :
    (A ⊗ₖ B) * (C ⊗ₖ D) * (E ⊗ₖ F) = (A * C * E) ⊗ₖ (B * D * F) := by
  rw [← Matrix.mul_kronecker_mul]
  rw [← Matrix.mul_kronecker_mul]

/-! ### W2. Two gates on the first part only: R1, then R4 on the second factor `1 * 1` -/
example {k l : Type} [Fintype k] [Fintype l] [DecidableEq l] (A C : Matrix k k ℂ) :
    (A ⊗ₖ (1 : Matrix l l ℂ)) * (C ⊗ₖ 1) = (A * C) ⊗ₖ 1 := by
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.one_mul]

/-! ### W3. What `⊗ₖ` means entrywise: `Matrix.kronecker_apply`
`(A ⊗ₖ B) (i, a) (j, b) = A i j * B a b`; rows and columns are indexed by pairs. -/
example {k l : Type} (A : Matrix k k ℂ) (B : Matrix l l ℂ) (i j : k) (a b : l) (P : ℂ → Prop)
    (h : P (A i j * B a b)) : P ((A ⊗ₖ B) (i, a) (j, b)) := by
  rw [Matrix.kronecker_apply]
  exact h

end E111Guide

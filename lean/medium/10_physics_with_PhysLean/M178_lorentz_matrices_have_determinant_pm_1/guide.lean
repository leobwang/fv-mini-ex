/- Guide for M178 (Lorentz matrices have determinant ±1).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. A hypothesis `k` or `h` in an entry is only there to finish the example; it shows what
the goal or hypothesis became. `G : Prop` is a goal the entry does not touch.
Part W: worked combinations on objects that are NOT the exercise's (an orthogonal matrix `Mᵀ * M = 1`,
the factor `2 ^ n` instead of `(-1) ^ d`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.LorentzGroup.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace M178Guide

/-! # Part R · Reference entries -/

/-! ## The defining identity and its determinant -/

/-! ### R1. `LorentzGroup.transpose_mul_minkowskiMatrix_mul_self` · context gains `Λᵀ * η * Λ = η`
`Λ` is an implicit argument: name it with `(Λ := Λ)`. -/
example {d : ℕ} (Λ : LorentzGroup d) (G : Prop) (k : (Λ.1)ᵀ * η * Λ.1 = η → G) : G := by
  have h := transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)
  exact k h

/-! ### R2. `congrArg Matrix.det h` · context gains `M.det = N.det` from `h : M = N`
`congrArg f : a = b → f a = f b` applies the same function to both sides of an equation. -/
example {n R : Type} [DecidableEq n] [Fintype n] [CommRing R] (M N : Matrix n n R) (h : M = N)
    (G : Prop) (k : M.det = N.det → G) : G := by
  have hd := congrArg Matrix.det h
  exact k hd

/-! ## Evaluating determinants inside a hypothesis -/

/-! ### R3. `Matrix.det_mul` · `(M * N).det = M.det * N.det` · context: `h` rewritten
`simp only [...] at h` fires as often as it can: `(M * N * K).det` needs it twice. -/
example {n R : Type} [DecidableEq n] [Fintype n] [CommRing R] (M N K : Matrix n n R) (P : R → Prop)
    (h : P (M * N * K).det) (G : Prop) (k : P (M.det * N.det * K.det) → G) : G := by
  simp only [Matrix.det_mul] at h
  exact k h

/-! ### R4. `Matrix.det_transpose` · `Mᵀ.det = M.det` · context: `h` rewritten -/
example {n R : Type} [DecidableEq n] [Fintype n] [CommRing R] (M : Matrix n n R) (P : R → Prop)
    (h : P Mᵀ.det) (G : Prop) (k : P M.det → G) : G := by
  simp only [Matrix.det_transpose] at h
  exact k h

/-! ### R5. `minkowskiMatrix.det_eq_neg_one_pow_d` · `η.det = (-1) ^ d` · context: `h` rewritten -/
example {d : ℕ} (P : ℝ → Prop) (h : P (minkowskiMatrix (d := d)).det) (G : Prop)
    (k : P ((-1) ^ d) → G) : G := by
  simp only [minkowskiMatrix.det_eq_neg_one_pow_d] at h
  exact k h

/-! ## Cancelling a nonzero factor -/

/-! ### R6. `linear_combination h` · closes `lhs = rhs` when `lhs - rhs = h.lhs - h.rhs` up to `ring`
`linear_combination e * h` uses `e` times `h` instead. -/
example (a b c : ℝ) (h : a * b * a = b + c) : b * (a * a - 1) = c := by
  linear_combination h

/-! ### R7. `pow_ne_zero` · `a ≠ 0 → a ^ n ≠ 0` · goal `a ^ n ≠ 0` → `a ≠ 0`
As a term: `pow_ne_zero n ha`, or `pow_ne_zero _ (by norm_num)` when `a` is a numeral. -/
example (a : ℝ) (n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by
  refine pow_ne_zero n ?_
  exact ha

/-! ### R8. `norm_num` · closes `(-1 : ℝ) ≠ 0` (a numeral inequality) -/
example : (-1 : ℝ) ≠ 0 := by
  norm_num

/-! ### R9. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0` · context gains the disjunction (`.mp h`) -/
example (a b : ℝ) (h : a * b = 0) (G : Prop) (k : a = 0 ∨ b = 0 → G) : G := by
  have hab := mul_eq_zero.mp h
  exact k hab

/-! ### R10. `Or.resolve_left` · `A ∨ B → ¬A → B` · context gains `B`
`a ≠ 0` is by definition `¬(a = 0)`, so it fits the `¬A` slot. -/
example (a b : ℝ) (hab : a = 0 ∨ b = 0) (ha : a ≠ 0) (G : Prop) (k : b = 0 → G) : G := by
  have hb := hab.resolve_left ha
  exact k hb

/-! ### R11. `linarith` · closes `x = 1` from `x - 1 = 0`; a product such as `a * a` counts as one unknown -/
example (a : ℝ) (h : a * a - 1 = 0) : a * a = 1 := by
  linarith

/-! ## From the square to the two values -/

/-! ### R12. `mul_self_eq_one_iff` · `a * a = 1 ↔ a = 1 ∨ a = -1` · goal `a = 1 ∨ a = -1` → `a * a = 1` -/
example {R : Type} [NonAssocRing R] [NoZeroDivisors R] (a : R) (h : a * a = 1) :
    a = 1 ∨ a = -1 := by
  refine mul_self_eq_one_iff.mp ?_
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An orthogonal matrix (`Mᵀ * M = 1`): R2, then R3 + R4 with `Matrix.det_one : (1 : Matrix n n R).det = 1`
in one `simp only … at h`, then R12 -/
example {n : Type} [DecidableEq n] [Fintype n] (M : Matrix n n ℝ) (hM : Mᵀ * M = 1) :
    M.det = 1 ∨ M.det = -1 := by
  have h := congrArg Matrix.det hM
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.mp h

/-! ### W2. Cancel the nonzero factor `2 ^ n`: R6, R7 + R8, R9 → R10, R11 -/
example (x : ℝ) (n : ℕ) (h : x * 2 ^ n * x = 2 ^ n) : x * x = 1 := by
  have h0 : (2 : ℝ) ^ n * (x * x - 1) = 0 := by linear_combination h
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 := (mul_eq_zero.mp h0).resolve_left h2
  linarith

end M178Guide

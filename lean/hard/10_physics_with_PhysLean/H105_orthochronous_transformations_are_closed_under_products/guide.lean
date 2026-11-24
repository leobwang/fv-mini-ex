/- Guide for H105 (Orthochronous transformations are closed under products).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis `h`): the step changes only the part shown
inside `P (…)`. A hypothesis `k : … → G` in an entry is only there to finish the example.
Part W: worked combinations on objects that are NOT the exercise's (orthogonal matrices, `η * η`,
other entries, an AM–GM bound).
Assumed: Lean basics.
-/
import Physlib.Relativity.LorentzGroup.Orthochronous.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace H105Guide

/-! # Part R · Reference entries -/

/-! ## A matrix identity → one scalar equation -/

/-! ### R1. `LorentzGroup.transpose_mul_minkowskiMatrix_mul_self` · context gains `Λᵀ * η * Λ = η`
`Λ` is an implicit argument: pass it by name, `(Λ := Λ)`. -/
example {d : ℕ} (Λ : LorentzGroup d) (G : Prop) (k : (Λ.1)ᵀ * η * Λ.1 = η → G) : G := by
  have h := transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)
  exact k h

/-! ### R2. `congrFun (congrFun h i) j` · context gains the `(i, j)` entry of a matrix equation
A matrix is a function of two indices, so `congrFun` (`f = g → f a = g a`) applied twice gives one
entry. -/
example {n : Type} (M N : Matrix n n ℝ) (h : M = N) (i j : n) (G : Prop) (k : M i j = N i j → G) :
    G := by
  have hij := congrFun (congrFun h i) j
  exact k hij

/-! ## Evaluating the entry (`simp [R3, R4, R7, R8] at h` also applies R5, R6, R9–R11 by itself) -/

/-! ### R3. `Matrix.mul_apply` · goal (or `at h`: context): entry of a product → a sum over the
middle index -/
example {n : Type} [Fintype n] (M N : Matrix n n ℝ) (i l : n) (P : ℝ → Prop)
    (h : P (∑ j, M i j * N j l)) : P ((M * N) i l) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R4. `Fintype.sum_sum_type` · goal (or `at h`: context): a sum over `Fin 1 ⊕ Fin d` → time
part + space part -/
example {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) (P : ℝ → Prop)
    (h : P (∑ a, f (Sum.inl a) + ∑ i, f (Sum.inr i))) : P (∑ x, f x) := by
  rw [Fintype.sum_sum_type]
  exact h

/-! ### R5. `Fin.sum_univ_one` · goal (or `at h`: context): a sum over `Fin 1` → its single term
`simp` reaches the same result with `Finset.univ_unique`, `Finset.sum_singleton`. -/
example (f : Fin 1 → ℝ) (P : ℝ → Prop) (h : P (f 0)) : P (∑ i, f i) := by
  rw [Fin.sum_univ_one]
  exact h

/-! ### R6. `Matrix.transpose_apply` · context: `Mᵀ i j` → `M j i` -/
example {n : Type} (M : Matrix n n ℝ) (i j : n) (P : ℝ → Prop) (h : P (Mᵀ i j)) (G : Prop)
    (k : P (M j i) → G) : G := by
  rw [Matrix.transpose_apply] at h
  exact k h

/-! ### R7. `minkowskiMatrix.as_diagonal` · context: `η` → `diagonal (Sum.elim 1 (-1))` -/
example {d : ℕ} (P : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ → Prop) (h : P η) (G : Prop)
    (k : P (diagonal (Sum.elim 1 (-1))) → G) : G := by
  rw [as_diagonal] at h
  exact k h

/-! ### R8. `Matrix.diagonal_apply` · context: entry of a diagonal matrix → an `if` -/
example {n : Type} [DecidableEq n] (v : n → ℝ) (i j : n) (P : ℝ → Prop)
    (h : P (diagonal v i j)) (G : Prop) (k : P (if i = j then v i else 0) → G) : G := by
  rw [Matrix.diagonal_apply] at h
  exact k h

/-! ### R9. `mul_ite`, `mul_zero` · context: a factor moves into both branches of an `if` -/
example (c x : ℝ) (p : Prop) [Decidable p] (P : ℝ → Prop) (h : P (c * if p then x else 0))
    (G : Prop) (k : P (if p then c * x else 0) → G) : G := by
  rw [mul_ite] at h
  rw [mul_zero] at h
  exact k h

/-! ### R10. `Finset.sum_ite_eq'` · goal (or `at h`: context): a sum of `if x = a then b x else 0`
→ `b a`. The lemma leaves `if a ∈ s then b a else 0`; `Finset.mem_univ` and `if_true` finish. -/
example {n : Type} [Fintype n] [DecidableEq n] (a : n) (b : n → ℝ) (P : ℝ → Prop)
    (h : P (b a)) : P (∑ x, if x = a then b x else 0) := by
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ### R11. `Sum.elim_inl`, `Sum.elim_inr`, `Pi.one_apply`, `Pi.neg_apply` · context: the diagonal
of `η` evaluated: `1` at time, `-1` at a space index -/
example {d : ℕ} (i : Fin d) (P : ℝ → ℝ → Prop)
    (h : P (Sum.elim (1 : Fin 1 → ℝ) (-1 : Fin d → ℝ) (Sum.inl 0))
      (Sum.elim (1 : Fin 1 → ℝ) (-1 : Fin d → ℝ) (Sum.inr i)))
    (G : Prop) (k : P 1 (-1) → G) : G := by
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, Pi.neg_apply] at h
  exact k h

/-! ## Closing the milestone equations -/

/-! ### R12. `simp only [_root_.sq]` · goal: `a ^ 2` → `a * a` (also under `∑`)
With `open minkowskiMatrix`, bare `sq` also means `minkowskiMatrix.sq : η * η = 1`: write `_root_.sq`. -/
example {n : Type} [Fintype n] (a : ℝ) (f : n → ℝ) (P : ℝ → ℝ → Prop)
    (h : P (a * a) (∑ i, f i * f i)) : P (a ^ 2) (∑ i, f i ^ 2) := by
  simp only [_root_.sq]
  exact h

/-! ### R13. `linear_combination h` · closes `L = R` when `L - R = h.lhs - h.rhs` as a ring identity -/
example (a s t : ℝ) (h : a * a + -s = t) : a * a = t + s := by
  linear_combination h

/-! ### R14. `LorentzGroup.mul_minkowskiMatrix_mul_transpose` · context gains `Λ * η * Λᵀ = η`
The same as R1 with the transpose on the other side; its entries are rows of `Λ`, not columns. -/
example {d : ℕ} (Λ : LorentzGroup d) (G : Prop) (k : Λ.1 * η * (Λ.1)ᵀ = η → G) : G := by
  have h := mul_minkowskiMatrix_mul_transpose (Λ := Λ)
  exact k h

/-! ### R15. `lorentzGroupIsGroup_mul_coe` · goal: the matrix of a product → product of matrices -/
example {d : ℕ} (A B : LorentzGroup d) (P : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ → Prop)
    (h : P (A.1 * B.1)) : P (A * B).1 := by
  rw [lorentzGroupIsGroup_mul_coe]
  exact h

/-! ## The inequality -/

/-! ### R16. `unfold IsOrthochronous at *` · goal and context: the predicate → the inequality
`IsOrthochronous Λ` is by definition `0 ≤ ↑Λ (Sum.inl 0) (Sum.inl 0)`. -/
example {d : ℕ} (Λ Λ' : LorentzGroup d) (h : IsOrthochronous Λ)
    (k : 0 ≤ Λ.1 (Sum.inl 0) (Sum.inl 0) → 0 ≤ Λ'.1 (Sum.inl 0) (Sum.inl 0)) :
    IsOrthochronous Λ' := by
  unfold IsOrthochronous at *
  exact k h

/-! ### R17. `Finset.sum_mul_sq_le_sq_mul_sq` · Cauchy–Schwarz for finite sums
Used forward, `have cs := Finset.sum_mul_sq_le_sq_mul_sq s f g` adds this statement to the context. -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 := by
  exact Finset.sum_mul_sq_le_sq_mul_sq s f g

/-! With `s := Finset.univ` and `fun` arguments, the sums are `∑ i, …` with the `fun` applied. -/
example {n : ℕ} (u v : Fin n → ℝ) : (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * ∑ i, v i ^ 2 := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => u i) (fun i => v i)

/-! ### R18. `sq_nonneg` · context gains `0 ≤ a ^ 2` -/
example (a : ℝ) (G : Prop) (k : 0 ≤ a ^ 2 → G) : G := by
  have h := sq_nonneg a
  exact k h

/-! ### R19. `Finset.sum_nonneg` · goal `0 ≤ ∑ i ∈ s, f i` → `∀ i ∈ s, 0 ≤ f i`
As a term: `Finset.sum_nonneg (fun i _ => sq_nonneg _)`. -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) : 0 ≤ ∑ i ∈ s, f i ^ 2 := by
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg (f i)

/-! ### R20. `generalize e = x at *` · goal and context: every copy of the term `e` → a new variable `x`
Afterwards `nlinarith` sees `x` as one unknown instead of a sum it cannot look into. -/
example {n : ℕ} (f : Fin n → ℝ) (h : 0 ≤ ∑ i, f i) (P : ℝ → Prop) (k : ∀ x, 0 ≤ x → P x) :
    P (∑ i, f i) := by
  generalize ∑ i, f i = x at *
  exact k x h

/-! ### R21. `nlinarith [t₁, …]` · closes a polynomial inequality over `ℝ`
It multiplies pairs of hypotheses (and the extra facts `tᵢ` you give it) before running `linarith`. -/
example (x y : ℝ) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  nlinarith

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y + x := by
  nlinarith [mul_nonneg hx hy]

/-! ### R22. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · context gains the product's sign -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (G : Prop) (k : 0 ≤ a * b → G) : G := by
  have hab := mul_nonneg ha hb
  exact k hab

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An entry of `Mᵀ * M = 1` (orthogonal, not Lorentz): R2, then `simp … at h`, R12, R13 -/
example {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hM : Mᵀ * M = 1) :
    M (Sum.inl 0) (Sum.inl 0) ^ 2 + ∑ i, M (Sum.inr i) (Sum.inl 0) ^ 2 = 1 := by
  have h := congrFun (congrFun hM (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simp only [_root_.sq]
  linear_combination h

/-! ### W2. An entry of `η * η` through the diagonal form: R3, R7, R8–R11 -/
example {d : ℕ} (i : Fin d) : (η * η : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (Sum.inr i) (Sum.inr i) = 1 := by
  simp [Matrix.mul_apply, as_diagonal, Matrix.diagonal_apply]

/-! ### W3. Another entry of a product in the Lorentz group: R15, R3, R4, R5 -/
example {d : ℕ} (A B : LorentzGroup d) (i : Fin d) :
    (A * B).1 (Sum.inr i) (Sum.inl 0)
      = A.1 (Sum.inr i) (Sum.inl 0) * B.1 (Sum.inl 0) (Sum.inl 0)
        + ∑ j, A.1 (Sum.inr i) (Sum.inr j) * B.1 (Sum.inr j) (Sum.inl 0) := by
  simp [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]

/-! ### W4. Cauchy–Schwarz, atoms, `nlinarith`: `∑ fᵢgᵢ ≤ (∑ fᵢ² + ∑ gᵢ²) / 2`: R17, R19, R20, R21 -/
example {n : ℕ} (f g : Fin n → ℝ) : (∑ i, f i * g i) ≤ (∑ i, f i ^ 2 + ∑ i, g i ^ 2) / 2 := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hA : 0 ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  generalize ∑ i, f i * g i = s at *
  generalize ∑ i, f i ^ 2 = A at *
  generalize ∑ i, g i ^ 2 = B at *
  nlinarith [sq_nonneg (A - B)]

end H105Guide

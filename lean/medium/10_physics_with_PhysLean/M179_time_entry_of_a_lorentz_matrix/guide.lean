/- Guide for M179 (Time entry of a Lorentz matrix).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. A hypothesis `k` or `h` in an entry is only there to finish the example; it shows what
the goal or hypothesis became. `G : Prop` is a goal the entry does not touch.
Part W: worked combinations on objects that are NOT the exercise's (a plain matrix `M`, `Mᵀ * M`,
`M * η`, a sum of squared differences).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.LorentzGroup.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace M179Guide

/-! # Part R · Reference entries -/

/-! ## From a matrix equation to one entry -/

/-! ### R1. `congrFun (congrFun h i) j` · context gains the entry equation `M i j = N i j` -/
example {m n α : Type} (M N : Matrix m n α) (h : M = N) (i : m) (j : n) (G : Prop)
    (k : M i j = N i j → G) : G := by
  have hij := congrFun (congrFun h i) j
  exact k hij

/-! ### R2. `LorentzGroup.transpose_mul_minkowskiMatrix_mul_self` · context gains `Λᵀ * η * Λ = η`
`Λ` is an implicit argument: name it with `(Λ := Λ)`. -/
example {d : ℕ} (Λ : LorentzGroup d) (G : Prop) (k : (Λ.1)ᵀ * η * Λ.1 = η → G) : G := by
  have h := transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)
  exact k h

/-! ### R3. `LorentzGroup.mul_minkowskiMatrix_mul_transpose` · context gains `Λ * η * Λᵀ = η` -/
example {d : ℕ} (Λ : LorentzGroup d) (G : Prop) (k : Λ.1 * η * (Λ.1)ᵀ = η → G) : G := by
  have h := mul_minkowskiMatrix_mul_transpose (Λ := Λ)
  exact k h

/-! ## Evaluating the entry (all used by `simp [...] at h`) -/

/-! ### R4. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index
`rw [Matrix.mul_apply] at h` (or `simp [Matrix.mul_apply] at h`) does the same inside `h`. -/
example {m n p α : Type} [Fintype n] [Mul α] [AddCommMonoid α] (M : Matrix m n α) (N : Matrix n p α)
    (i : m) (l : p) (P : α → Prop) (h : P (∑ j, M i j * N j l)) : P ((M * N) i l) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R5. `Matrix.transpose_apply` · goal: entry `(i, j)` of `Mᵀ` → entry `(j, i)` of `M` -/
example {m n α : Type} (M : Matrix m n α) (i : n) (j : m) (P : α → Prop) (h : P (M j i)) :
    P (Mᵀ i j) := by
  rw [Matrix.transpose_apply]
  exact h

/-! ### R6. `minkowskiMatrix.as_diagonal` · goal: `η` → `diagonal (Sum.elim 1 (-1))` -/
example {d : ℕ} (i j : Fin 1 ⊕ Fin d) (P : ℝ → Prop) (h : P (diagonal (Sum.elim 1 (-1)) i j)) :
    P (η i j) := by
  rw [minkowskiMatrix.as_diagonal]
  exact h

/-! ### R7. `Matrix.diagonal_apply` · goal: entry of `diagonal c` → `if i = j then c i else 0` -/
example {n α : Type} [DecidableEq n] [Zero α] (c : n → α) (i j : n) (P : α → Prop)
    (h : P (if i = j then c i else 0)) : P (diagonal c i j) := by
  rw [Matrix.diagonal_apply]
  exact h

/-! ### R8. `mul_ite`, `mul_zero`, `Finset.sum_ite_eq'`, `Finset.mem_univ` · goal: a sum with
`if j = l` in each term → its `l`-th term -/
example {n : Type} [Fintype n] [DecidableEq n] (f c : n → ℝ) (l : n) (P : ℝ → Prop)
    (h : P (f l * c l)) : P (∑ j, f j * (if j = l then c j else 0)) := by
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ### R9. `Fintype.sum_sum_type` · goal: a sum over `α ⊕ β` → the `inl` part plus the `inr` part -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α ⊕ β → M) (P : M → Prop)
    (h : P (∑ a, f (Sum.inl a) + ∑ b, f (Sum.inr b))) : P (∑ x, f x) := by
  rw [Fintype.sum_sum_type]
  exact h

/-! ### R10. `Fin.sum_univ_one` · goal: a sum over `Fin 1` → its only term
`simp` reaches the same result through `Finset.univ_unique` and `Finset.sum_singleton`. -/
example {M : Type} [AddCommMonoid M] (f : Fin 1 → M) (P : M → Prop) (h : P (f 0)) :
    P (∑ a, f a) := by
  rw [Fin.sum_univ_one]
  exact h

/-! ### R11. `Sum.elim_inl`, `Sum.elim_inr`, `Pi.one_apply`, `Pi.neg_apply` · goal: the diagonal of `η`
`Sum.elim f g` is `f` on `Sum.inl _` and `g` on `Sum.inr _`; `1`, `-1` here are constant functions. -/
example {d : ℕ} (a : Fin 1) (i : Fin d) (P : ℝ → ℝ → Prop) (h : P 1 (-1)) :
    P (Sum.elim (1 : Fin 1 → ℝ) (-1 : Fin d → ℝ) (Sum.inl a))
      (Sum.elim (1 : Fin 1 → ℝ) (-1 : Fin d → ℝ) (Sum.inr i)) := by
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [Pi.one_apply, Pi.neg_apply]
  exact h

/-! ## From the entry equation to a statement about squares -/

/-! ### R12. `_root_.sq` · goal: `a ^ 2` → `a * a`, also under `∑`
With `open minkowskiMatrix`, a bare `sq` is `minkowskiMatrix.sq : η * η = 1`. Write `_root_.sq`. -/
example {d : ℕ} (a : ℝ) (f : Fin d → ℝ) (P : ℝ → ℝ → Prop) (h : P (a * a) (∑ i, f i * f i)) :
    P (a ^ 2) (∑ i, f i ^ 2) := by
  simp only [_root_.sq]
  exact h

/-! ### R13. `linear_combination h` · closes `lhs = rhs` when `lhs - rhs` is `h.lhs - h.rhs` up to `ring` -/
example (a b c : ℝ) (h : a + -b = c) : a = c + b := by
  linear_combination h

/-! ### R14. `Finset.sum_nonneg` · goal `0 ≤ ∑ i ∈ s, f i` → `∀ i ∈ s, 0 ≤ f i`
`∑ i, f i` is `∑ i ∈ Finset.univ, f i`. As a term: `Finset.sum_nonneg (fun i _ => …)`. -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) : 0 ≤ ∑ i, f i := by
  apply Finset.sum_nonneg
  exact fun i _ => hf i

/-! ### R15. `sq_nonneg` · closes `0 ≤ a ^ 2` -/
example (a : ℝ) : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

/-! ## Splitting the goal and closing the first half -/

/-! ### R16. `refine ⟨?_, fun h1 i => ?_⟩` · goal list: `A ∧ (B → ∀ i, C i)` → `⊢ A` and
`h1 : B, i : ι ⊢ C i` -/
example {ι : Type} (A B : Prop) (C : ι → Prop) (ha : A) (hc : B → ∀ i, C i) :
    A ∧ (B → ∀ i, C i) := by
  refine ⟨?_, fun h1 i => ?_⟩
  exact ha
  exact hc h1 i

/-! ### R17. `one_le_sq_iff_one_le_abs` · `1 ≤ a ^ 2 ↔ 1 ≤ |a|`; with `.mp ?_`, goal `1 ≤ |a|` → `1 ≤ a ^ 2` -/
example {α : Type} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (a : α) (h : 1 ≤ a ^ 2) :
    1 ≤ |a| := by
  refine (one_le_sq_iff_one_le_abs a).mp ?_
  exact h

/-! ### R18. `linarith` · closes a linear (in)equality that follows from linear hypotheses;
`a ^ 2` and `∑ i, f i ^ 2` count as unknowns -/
example {d : ℕ} (a : ℝ) (f : Fin d → ℝ) (h1 : a ^ 2 = 1 + ∑ i, f i ^ 2) (h2 : 0 ≤ ∑ i, f i ^ 2) :
    1 ≤ a ^ 2 := by
  linarith

/-! ## Second half: zero sums of squares -/

/-! ### R19. `rw [h] at h₁ h₂` · context: `a` → `b` in both hypotheses -/
example (a b : ℝ) (P Q : ℝ → Prop) (h : a = b) (h₁ : P a) (h₂ : Q a) (G : Prop)
    (k : P b → Q b → G) : G := by
  rw [h] at h₁ h₂
  exact k h₁ h₂

/-! ### R20. `Finset.sum_eq_zero_iff_of_nonneg` · `(∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)`
· goal: a zero sum of nonnegative terms → every term is zero. `… at h` does it inside `h`. -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (h : ∀ i ∈ Finset.univ, f i ^ 2 = 0) :
    ∑ i, f i ^ 2 = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  exact h

/-! ### R21. `Finset.mem_univ` · `Finset.mem_univ i : i ∈ Finset.univ`; context gains `h i (Finset.mem_univ i)` -/
example {ι : Type} [Fintype ι] (Q : ι → Prop) (h : ∀ i ∈ Finset.univ, Q i) (i : ι) (G : Prop)
    (k : Q i → G) : G := by
  have hi := h i (Finset.mem_univ i)
  exact k hi

/-! ### R22. `pow_eq_zero_iff` · `n ≠ 0 → (a ^ n = 0 ↔ a = 0)`; `two_ne_zero : 2 ≠ 0`
· goal `a = 0` → `a ^ 2 = 0` with `.mp ?_` -/
example (a : ℝ) (h : a ^ 2 = 0) : a = 0 := by
  refine (pow_eq_zero_iff two_ne_zero).mp ?_
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An orthogonal `M` (`Mᵀ * M = 1`, no `η`) has `M⁰₀ ^ 2 ≤ 1`:
R1, then `simp` with R4, R5, R9, R10; then R12 → R13, R14 + R15, R18 -/
example {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hM : Mᵀ * M = 1) :
    M (Sum.inl 0) (Sum.inl 0) ^ 2 ≤ 1 := by
  have h := congrFun (congrFun hM (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type] at h
  have hs : 0 ≤ ∑ i, M (Sum.inr i) (Sum.inl 0) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have e : M (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 - ∑ i, M (Sum.inr i) (Sum.inl 0) ^ 2 := by
    simp only [_root_.sq]; linear_combination h
  linarith

/-! ### W2. The `(0, 0)` entry of `M * η`: R4, R6, R7, R8, R11 in one `simp` -/
example {d : ℕ} (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (c : ℝ) (hM : M * η = c • 1) :
    M (Sum.inl 0) (Sum.inl 0) = c := by
  have h := congrFun (congrFun hM (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at h
  exact h

/-! ### W3. A zero sum of squared differences forces equal entries: R20, R21, R22 -/
example {ι : Type} [Fintype ι] (f g : ι → ℝ) (h : ∑ i, (f i - g i) ^ 2 = 0) (i : ι) :
    f i = g i := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h
  have hi := h i (Finset.mem_univ i)
  have h0 := (pow_eq_zero_iff two_ne_zero).mp hi
  linarith

end M179Guide

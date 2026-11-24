/- Guide for M126 (The Hadamard gate).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (√3, other matrices).
Assumed: Lean basics.
-/
import Mathlib

open Matrix Complex

namespace M126Guide

/-! # Part R · Reference entries -/

/-! ## Splitting the goal and adding facts -/

/-! ### R1. `refine ⟨?_, ?_, ?_, ?_⟩` · goal → four goals -/
example (A B C D : Prop) (ha : A) (hb : B) (hc : C) (hd : D) : A ∧ B ∧ C ∧ D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  exacts [ha, hb, hc, hd]

/-! ### R2. `have h : T := proof` · context gains `h : T`; goal unchanged -/
example (T G : Prop) (t : T) (g : T → G) : G := by
  have h : T := t
  exact g h

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

/-! ## Evaluating one entry (`simp` applies these by itself) -/

/-! ### R5. Unfold a definition: `simp only [D]` · goal: the name `D` → its body -/
def D : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 4]
example (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P !![1, 2; 3, 4]) : P D := by
  simp only [D]
  exact h

/-! ### R6. Entry of a literal `!![a, b; c, d] i j` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P b) : P (!![a, b; c, d] 0 1) := by
  simp
  exact h

/-! ### R7. `Matrix.smul_apply`, `smul_eq_mul` · goal: entry of `c • M` → `c * (entry of M)` -/
example (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (P : ℂ → Prop) (h : P (c * M i j)) :
    P ((c • M) i j) := by
  rw [Matrix.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R8. `Matrix.one_apply_eq`, `Matrix.one_apply_ne` · goal: entries of the identity `1` -/
example (P : ℂ → Prop) (h1 : P 1) (h0 : P 0) :
    P ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∧ P ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  simp
  exact ⟨h1, h0⟩

/-! ### R9. `Matrix.neg_apply` · goal: entry of `-M` → `-(entry of M)` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (P : ℂ → Prop) (h : P (-M i j)) :
    P ((-M) i j) := by
  rw [Matrix.neg_apply]
  exact h

/-! ### R10. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R11. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R12. `Matrix.vecMul`, `dotProduct` · goal: `v ᵥ* M` (row vector times matrix) → a sum
This is the form `simp` gets stuck on when `Mᴴ` is involved (W4). -/
example (v : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) (P : ℂ → Prop)
    (h : P (v 0 * M 0 j + v 1 * M 1 j)) : P ((v ᵥ* M) j) := by
  simp only [Matrix.vecMul]
  simp only [dotProduct]
  simp only [Fin.sum_univ_two]
  exact h

/-! ## Scalars: inverses, casts, square roots -/

/-! ### R13. `mul_inv` · `(a * b)⁻¹ = a⁻¹ * b⁻¹`; used right to left: `rw [← mul_inv]` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (P : α → Prop) (h : P (a * b)⁻¹) :
    P (a⁻¹ * b⁻¹) := by
  rw [← mul_inv]
  exact h

/-! ### R14. `Complex.ofReal_mul` · `↑(x * y) = ↑x * ↑y`; right to left moves `*` inside the cast -/
example (x y : ℝ) (P : ℂ → Prop) (h : P ↑(x * y)) : P (↑x * ↑y) := by
  rw [← Complex.ofReal_mul]
  exact h

/-! ### R15. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x` · goal rewritten, plus side goal `0 ≤ x`
Write `rw [Real.mul_self_sqrt (by norm_num)]` to close the side goal on the spot. -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x * √x) := by
  rw [Real.mul_self_sqrt]
  exact h
  exact hx

/-! ### R16. `inv_pow` · `a⁻¹ ^ n = (a ^ n)⁻¹` -/
example {α : Type} [DivisionMonoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n)⁻¹) :
    P (a⁻¹ ^ n) := by
  rw [inv_pow]
  exact h

/-! ### R17. `Complex.ofReal_pow` · `↑(x ^ n) = ↑x ^ n`; right to left moves `^` inside the cast -/
example (x : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P ↑(x ^ n)) : P (↑x ^ n) := by
  rw [← Complex.ofReal_pow]
  exact h

/-! ### R18. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! ### R19. `ring_nf` · goal put in ring normal form: `a * a` → `a ^ 2` -/
example (a : ℂ) (P : ℂ → Prop) (h : P (a ^ 2)) : P (a * a) := by
  ring_nf
  exact h

/-! ### R20. `norm_num` · closes a goal made of numerals (`⁻¹`, `/`, casts of numerals included) -/
example : ((3 : ℝ) : ℂ)⁻¹ = 1 / 3 := by norm_num

/-! ### R25. `mul_right_comm` · `a * b * c = a * c * b` · goal: swap the last two factors
`rw [mul_right_comm _ b]` fixes the middle factor `b`, so only products with `b` in the middle move. -/
example {α : Type} [CommMonoid α] (a b c : α) (P : α → Prop) (h : P (a * c * b)) : P (a * b * c) := by
  rw [mul_right_comm _ b]
  exact h

/-! ### R26. `ring` · closes an identity of commutative rings; treats `I`, `√x`, `x⁻¹` as unknowns -/
example (a : ℂ) : 1 / 2 * a + 1 / 2 * a = a := by ring

/-! ## Unitarity and conjugation -/

/-! ### R21. `Matrix.mem_unitaryGroup_iff` · goal: membership → an equation -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M * star M = 1) : M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact h

/-! ### R22. `Matrix.star_eq_conjTranspose` · goal: `star M` → `Mᴴ` (conjugate transpose) -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P Mᴴ) :
    P (star M) := by
  rw [Matrix.star_eq_conjTranspose]
  exact h

/-! ### R23. `Matrix.conjTranspose_apply` · goal: entry `(i, j)` of `Mᴴ` → `star` of entry `(j, i)` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (P : ℂ → Prop) (h : P (star (M j i))) :
    P (Mᴴ i j) := by
  rw [Matrix.conjTranspose_apply]
  exact h

/-! ### R24. `Complex.conj_ofReal` · goal: conjugate of a real cast → the cast itself
`(starRingEnd ℂ) z` is Lean's name for the complex conjugate `conj z`. -/
example (r : ℝ) (P : ℂ → Prop) (h : P ↑r) : P ((starRingEnd ℂ) ↑r) := by
  rw [Complex.conj_ofReal]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `ext` + `fin_cases` on named matrices, then `simp [names]` -/
def A : Matrix (Fin 2) (Fin 2) ℂ := !![2, 0; 0, 3]
def B : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]
example : A * B = !![2, 2; 0, 3] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [A, B]

/-! ### W2. What `simp` leaves when the scalar is a real square root: always `s * s`, never `s ^ 2` -/
noncomputable def K : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 3)⁻¹ : ℂ) • !![1, 0; 0, 1]
example : K * K = !![1/3, 0; 0, 1/3] := by
  have h : (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = 1 / 3 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> simp [K]
  all_goals rw [h]; norm_num

/-! ### W3. The square-root fact as one chain: R13, R14, R15, R20 -/
example : (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = 1 / 3 := by
  rw [← mul_inv]
  rw [← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (by norm_num)]
  norm_num

/-! ### W4. With `ᴴ`, plain `simp [S]` stops at `v ᵥ* Mᴴ` (R12); give it R10 and R11 from the start -/
def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, I]
example : S * Sᴴ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S]
  all_goals simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

example : S ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]

end M126Guide

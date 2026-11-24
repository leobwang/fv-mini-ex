/- Guide for H088 (Time evolution: exp(−iθX/2) and unitarity).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other units, `Fin 3`, `e^{+ix}`).
Assumed: Lean basics. `NormedSpace.exp` is written out in full: with `open Complex`, a bare `exp` is the
scalar `Complex.exp` and does not apply to matrices.
-/
import Mathlib

open Matrix Complex

namespace H088Guide

/-! # Part R · Reference entries -/

/-! ## Units, matrix equations, entries -/

/-! ### R1. `refine ⟨a, b, ?_, ?_⟩` for a unit `αˣ` · goal list: one goal per proof field
A unit is the structure `⟨val, inv, val_inv, inv_val⟩`. In a term you write `by …` in each `?_` slot. -/
example {α : Type} [Monoid α] (a b : α) (h₁ : a * b = 1) (h₂ : b * a = 1) : αˣ := by
  refine ⟨a, b, ?_, ?_⟩
  exacts [h₁, h₂]

/-! ### R2. `ext i j` (lemma `Matrix.ext`) · goal `M = N` → context gains `i j`, goal is one entry -/
example {α : Type} (M N : Matrix (Fin 2) (Fin 2) α) (h : ∀ i j, M i j = N i j) : M = N := by
  ext i j
  exact h i j

/-! ### R3. `fin_cases i` · context loses `i : Fin 2`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`. -/
example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  fin_cases i
  exacts [h0, h1]

/-! ### R4. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R5. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R6. `simp` on an entry of `c • !![…]` · goal: entry of a scaled literal → a product -/
example (c a b d e : ℂ) (P : ℂ → Prop) (h : P (c * b)) : P ((c • !![a, b; d, e]) 0 1) := by
  simp
  exact h

/-! ### R7. `norm_num` · closes a goal made of numerals (`⁻¹`, `/` included) -/
example : (3 : ℂ)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by norm_num

/-! ## Unfolding a unit, diagonal matrices -/

/-! ### R8. `Units.val_mk` · goal: the matrix of `⟨a, b, h₁, h₂⟩` → `a` -/
example {α : Type} [Monoid α] (a b : α) (h₁ : a * b = 1) (h₂ : b * a = 1) (P : α → Prop)
    (h : P a) : P ↑(Units.mk a b h₁ h₂) := by
  rw [Units.val_mk]
  exact h

/-! ### R9. `Units.inv_mk` (then R8) · goal: the matrix of `⟨a, b, h₁, h₂⟩⁻¹` → `b` -/
example {α : Type} [Monoid α] (a b : α) (h₁ : a * b = 1) (h₂ : b * a = 1) (P : α → Prop)
    (h : P b) : P ↑(Units.mk a b h₁ h₂)⁻¹ := by
  simp only [Units.inv_mk, Units.val_mk]
  exact h

/-! ### R10. `Matrix.vecMul_diagonal` · goal: `(v ᵥ* diagonal w) x` → `v x * w x`
`v ᵥ* M` is the row vector `v` times the matrix `M`; `simp` leaves products with a `diagonal` in
this form (W4). -/
example (v w : Fin 2 → ℂ) (x : Fin 2) (P : ℂ → Prop) (h : P (v x * w x)) :
    P ((v ᵥ* diagonal w) x) := by
  rw [Matrix.vecMul_diagonal]
  exact h

/-! ### R11. `ring` · closes a commutative-ring identity; numerals like `2⁻¹` are fine -/
example (a b : ℂ) : (a + b) * 2⁻¹ + (a - b) * 2⁻¹ = a := by ring

/-! ## The exponential of a diagonal matrix -/

/-! ### R12. `Matrix.exp_diagonal` · goal: `exp (diagonal v)` → `diagonal (exp v)` -/
example {m : Type} [Fintype m] [DecidableEq m] (v : m → ℂ) (P : Matrix m m ℂ → Prop)
    (h : P (diagonal (NormedSpace.exp v))) : P (NormedSpace.exp (diagonal v)) := by
  rw [Matrix.exp_diagonal]
  exact h

/-! ### R13. `Pi.exp_def` · goal: `exp` of a vector → the vector of entrywise `exp` -/
example {m : Type} [Fintype m] (v : m → ℂ) (P : (m → ℂ) → Prop)
    (h : P (fun i => NormedSpace.exp (v i))) : P (NormedSpace.exp v) := by
  rw [Pi.exp_def]
  exact h

/-! ### R14. `simp only [← Complex.exp_eq_exp_ℂ]` · goal: scalar `NormedSpace.exp` → `cexp`
`Complex.exp_eq_exp_ℂ : cexp = NormedSpace.exp`. `simp only` (not `rw`) can rewrite under `fun i =>`. -/
example {m : Type} (v : m → ℂ) (P : (m → ℂ) → Prop) (h : P (fun i => cexp (v i))) :
    P (fun i => NormedSpace.exp (v i)) := by
  simp only [← Complex.exp_eq_exp_ℂ]
  exact h

/-! ## Conjugate transposes of scalar multiples -/

/-! ### R15. `Matrix.conjTranspose_smul` · goal: `(c • M)ᴴ` → `star c • Mᴴ` -/
example {m : Type} (c : ℂ) (M : Matrix m m ℂ) (P : Matrix m m ℂ → Prop) (h : P (star c • Mᴴ)) :
    P (c • M)ᴴ := by
  rw [Matrix.conjTranspose_smul]
  exact h

/-! ### R16. `hM.eq` for `hM : M.IsHermitian` · goal: `Mᴴ` → `M` -/
example {m : Type} (M : Matrix m m ℂ) (hM : M.IsHermitian) (P : Matrix m m ℂ → Prop) (h : P M) :
    P Mᴴ := by
  rw [hM.eq]
  exact h

/-! ### R17. `neg_smul` · `-c • M = -(c • M)`; right to left: `rw [← neg_smul]` -/
example {m : Type} (c : ℂ) (M : Matrix m m ℂ) (P : Matrix m m ℂ → Prop) (h : P (-c • M)) :
    P (-(c • M)) := by
  rw [← neg_smul]
  exact h

/-! ### R18. `congr 1` · goal `f a = f b` → `a = b` (here: equal scalars give equal multiples) -/
example {m : Type} (c d : ℂ) (M : Matrix m m ℂ) (h : True → c = d) : c • M = d • M := by
  congr 1
  exact h trivial

/-! ### R19. `Complex.star_def` · goal: `star z` → `(starRingEnd ℂ) z`, the complex conjugate -/
example (z : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z)) : P (star z) := by
  rw [Complex.star_def]
  exact h

/-! ### R20. `map_mul` · goal: conjugate of a product → product of conjugates -/
example (z w : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z * (starRingEnd ℂ) w)) :
    P ((starRingEnd ℂ) (z * w)) := by
  rw [map_mul]
  exact h

/-! ### R21. `Complex.conj_ofReal`, `Complex.conj_I` · goal: `conj ↑r` → `↑r`, `conj I` → `-I` -/
example (r : ℝ) (P : ℂ → Prop) (h : P (↑r * -I)) :
    P ((starRingEnd ℂ) ↑r * (starRingEnd ℂ) I) := by
  rw [Complex.conj_ofReal, Complex.conj_I]
  exact h

/-! ### R22. `simp` · closes a scalar `star` goal built from `↑r`, `I`, `-`, `*` (it applies R19–R21) -/
example (r : ℝ) : star ((r : ℂ) * I) = -((r : ℂ) * I) := by simp

/-! ## Evaluating the phases e^{±ix} -/

/-! ### R23. `Matrix.exp_units_conj` · goal: `exp (U A U⁻¹)` → `U (exp A) U⁻¹` -/
example {m : Type} [Fintype m] [DecidableEq m] (U : (Matrix m m ℂ)ˣ) (A : Matrix m m ℂ)
    (P : Matrix m m ℂ → Prop)
    (h : P ((U : Matrix m m ℂ) * NormedSpace.exp A * (↑U⁻¹ : Matrix m m ℂ))) :
    P (NormedSpace.exp ((U : Matrix m m ℂ) * A * (↑U⁻¹ : Matrix m m ℂ))) := by
  rw [Matrix.exp_units_conj]
  exact h

/-! ### R24. `funext i` · goal: equality of functions → equality at a fresh `i` -/
example (f g : Fin 2 → ℂ) (h : ∀ i, f i = g i) : f = g := by
  funext i
  exact h i

/-! ### R25. `simp only [Fin.zero_eta, Matrix.cons_val_zero]` (index 0) and
`simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]` (index 1) · goal: entry of
`![a, b]` at an index printed by `fin_cases` → `a` or `b` -/
example {α : Type} (a b : α) (P : α → Prop) (ha : P a) (hb : P b) (i : Fin 2) : P (![a, b] i) := by
  fin_cases i
  simp only [Fin.zero_eta, Matrix.cons_val_zero]
  exact ha
  simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact hb

/-! ### R26. `Complex.exp_mul_I` · goal: `cexp (x * I)` → `cos x + sin x * I` (Euler) -/
example (x : ℂ) (P : ℂ → Prop) (h : P (cos x + sin x * I)) : P (cexp (x * I)) := by
  rw [Complex.exp_mul_I]
  exact h

/-! ### R27. `Complex.cos_neg`, `Complex.sin_neg` · goal: `cos (-x)` → `cos x`, `sin (-x)` → `-sin x` -/
example (x : ℂ) (P : ℂ → Prop) (h : P (cos x + -sin x * I)) : P (cos (-x) + sin (-x) * I) := by
  simp only [Complex.cos_neg, Complex.sin_neg]
  exact h

/-! ### R28. `neg_mul`, `neg_neg` · goal: `-(-a * b)` → `a * b` -/
example (a b : ℂ) (P : ℂ → Prop) (h : P (a * b)) : P (-(-a * b)) := by
  simp only [neg_mul, neg_neg]
  exact h

/-! ### R29. `Complex.ofReal_cos`, `Complex.ofReal_sin` · goal: `↑(Real.cos x)` → `cos ↑x`
`simp` applies these by itself, so the `Real.cos` entries of a matrix meet the `cos` of the phases. -/
example (x : ℝ) (P : ℂ → Prop) (h : P (cos ↑x * sin ↑x)) :
    P (↑(Real.cos x) * ↑(Real.sin x)) := by
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  exact h

/-! ## Unitarity of an exponential -/

/-! ### R30. `Matrix.mem_unitaryGroup_iff` · goal: membership → an equation -/
example {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (h : M * star M = 1) :
    M ∈ Matrix.unitaryGroup m ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact h

/-! ### R31. `Matrix.star_eq_conjTranspose` · goal: `star M` → `Mᴴ` -/
example {m : Type} (M : Matrix m m ℂ) (P : Matrix m m ℂ → Prop) (h : P Mᴴ) : P (star M) := by
  rw [Matrix.star_eq_conjTranspose]
  exact h

/-! ### R32. `Matrix.exp_conjTranspose` · `exp Aᴴ = (exp A)ᴴ`; right to left moves `ᴴ` inside -/
example {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (P : Matrix m m ℂ → Prop)
    (h : P (NormedSpace.exp Aᴴ)) : P (NormedSpace.exp A)ᴴ := by
  rw [← Matrix.exp_conjTranspose]
  exact h

/-! ### R33. `(Commute.refl A).neg_right` · context gains `Commute A (-A)`
`Commute A B` means `A * B = B * A`. `Commute.refl A : Commute A A`; `.neg_right` negates the right side. -/
example {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (G : Prop)
    (g : Commute A (-A) → G) : G := by
  have hc : Commute A (-A) := (Commute.refl A).neg_right
  exact g hc

/-! ### R34. `Matrix.exp_add_of_commute` · `Commute A B → exp (A + B) = exp A * exp B`
Right to left, with the commuting proof given: `rw [← Matrix.exp_add_of_commute _ _ hc]`. -/
example {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) (hc : Commute A B)
    (P : Matrix m m ℂ → Prop) (h : P (NormedSpace.exp (A + B))) :
    P (NormedSpace.exp A * NormedSpace.exp B) := by
  rw [← Matrix.exp_add_of_commute _ _ hc]
  exact h

/-! ### R35. `add_neg_cancel` · goal: `A + -A` → `0` -/
example {m : Type} (A : Matrix m m ℂ) (P : Matrix m m ℂ → Prop) (h : P 0) : P (A + -A) := by
  rw [add_neg_cancel]
  exact h

/-! ### R36. `NormedSpace.exp_zero` · goal: `exp 0` → `1` -/
example {m : Type} [Fintype m] [DecidableEq m] (P : Matrix m m ℂ → Prop) (h : P 1) :
    P (NormedSpace.exp 0) := by
  rw [NormedSpace.exp_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Conjugation then a diagonal exponential, on `Fin 3`: R23, R12, R13, R14 -/
example (U : (Matrix (Fin 3) (Fin 3) ℂ)ˣ) (v : Fin 3 → ℂ) :
    NormedSpace.exp ((U : Matrix (Fin 3) (Fin 3) ℂ) * diagonal v * (↑U⁻¹ : Matrix (Fin 3) (Fin 3) ℂ)) =
      (U : Matrix (Fin 3) (Fin 3) ℂ) * diagonal (fun i => cexp (v i)) *
        (↑U⁻¹ : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [Matrix.exp_units_conj]
  rw [Matrix.exp_diagonal]
  rw [Pi.exp_def]
  simp only [← Complex.exp_eq_exp_ℂ]

/-! ### W2. The phases `e^{+ix}, e^{-ix}` as cos/sin: R24, R3, R25, R26–R28, R11 -/
example (x : ℂ) : (fun i => cexp (![x * I, -(x * I)] i)) = ![cos x + sin x * I, cos x - sin x * I] := by
  funext i
  fin_cases i
  simp only [Fin.zero_eta, Matrix.cons_val_zero, Complex.exp_mul_I]
  simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, ← neg_mul, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

/-! ### W3. `exp (-A) * exp A = 1` for any square matrix: R33 (with `neg_left`), R34, `neg_add_cancel`, R36 -/
example {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_left)]
  rw [neg_add_cancel]
  rw [NormedSpace.exp_zero]

/-! ### W4. Conjugating a diagonal by an explicit unit: `simp [U]` stops at `v ᵥ* diagonal w` (R10) -/
def U2 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]⟩

example (a b : ℂ) :
    (U2 : Matrix (Fin 2) (Fin 2) ℂ) * diagonal ![a, b] * (↑U2⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) =
      !![a, b - a; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [Matrix.vecMul_diagonal]
  all_goals ring

end H088Guide

/- Guide for H078 (Concurrence and reduced purity).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (one-qubit kets, other complex
identities, other matrices).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Mixed.MState

open scoped Matrix

namespace H078Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · The entries of `Tr_B |ψ⟩⟨ψ|` (milestone `traceRight_pure_apply`) -/

/-! ### R1. `show G'` · goal: replaced by a definitionally equal goal `G'`
`ρ.m` is *defined* as `ρ.M.mat` (the matrix inside the Hermitian matrix inside the state), which
Lean prints `↑↑ρ`. `rw` only sees the printed form, so first `show` the form the next lemma expects. -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (i j : d) (P : ℂ → Prop)
    (h : P (ρ.M.mat i j)) : P (ρ.m i j) := by
  show P (ρ.M.mat i j)
  exact h

/-! ### R2. `MState.traceRight_M` · goal: `↑ρ.traceRight` → `(↑ρ).traceRight`
Taking the partial trace of the state, then its Hermitian matrix `↑` (= `.M`), is the same as taking
the Hermitian matrix first and then its partial trace. -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ : MState (d₁ × d₂)) (P : HermitianMat d₁ ℂ → Prop) (h : P ρ.M.traceRight) :
    P ρ.traceRight.M := by
  rw [MState.traceRight_M]
  exact h

/-! ### R3. `HermitianMat.traceRight_mat` · goal: `↑A.traceRight` → `(↑A).traceRight`
The same commutation one level down: Hermitian matrix `A` → plain matrix `↑A` (= `A.mat`). -/
example {d₁ d₂ : Type} [Fintype d₂] (A : HermitianMat (d₁ × d₂) ℂ) (P : Matrix d₁ d₁ ℂ → Prop)
    (h : P A.mat.traceRight) : P A.traceRight.mat := by
  rw [HermitianMat.traceRight_mat]
  exact h

/-! ### R4. `MState.mat_M` · goal: `↑↑ρ` → `ρ.m` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (P : Matrix d d ℂ → Prop)
    (h : P ρ.m) : P ρ.M.mat := by
  rw [MState.mat_M]
  exact h

/-! ### R5. `simp only [Matrix.traceRight, Matrix.of_apply]` · goal: entry of a partial trace → a sum
`Matrix.traceRight M = Matrix.of fun i j => ∑ k, M (i, k) (j, k)` (sum over the second factor).
`Matrix.of f` is the matrix with entries `f i j`; `Matrix.of_apply` evaluates it. -/
example {d₁ d₂ : Type} [Fintype d₂] (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (i j : d₁) (P : ℂ → Prop)
    (h : P (∑ k, M (i, k) (j, k))) : P (M.traceRight i j) := by
  simp only [Matrix.traceRight, Matrix.of_apply]
  exact h

/-! ### R6. `MState.pure_apply` · goal: `(MState.pure ψ).m i j` → `ψ i * (starRingEnd ℂ) (ψ j)`
`MState.pure ψ` is `|ψ⟩⟨ψ|`; its entry is `ψᵢ ψ̄ⱼ`. `(starRingEnd ℂ) z` is the conjugate `z̄`.
Use `simp only`: inside a `∑ k, …` the entry sits under a binder, where `rw` cannot reach. -/
example {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i j : d) (P : ℂ → Prop)
    (h : P (ψ i * starRingEnd ℂ (ψ j))) : P ((MState.pure ψ).m i j) := by
  simp only [MState.pure_apply]
  exact h

/-! ## Part 2 · Purity as a trace (milestone `purity_eq`) -/

section purity
-- `inner Prob ρ σ` needs the instance `MState` declares as `scoped`; only the guide writes it
open scoped MState

/-! ### R7. `simp only [MState.purity]` · goal: `ρ.purity` → `⟪ρ, ρ⟫_Prob`
`ρ.purity : Prob` is defined as the Hilbert–Schmidt inner product of `ρ` with itself, packaged as a
`Prob` (a real number in `[0, 1]`). -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (P : Prob → Prop)
    (h : P (inner Prob ρ ρ)) : P ρ.purity := by
  simp only [MState.purity]
  exact h

/-! ### R8. `MState.val_inner` · goal: `↑⟪ρ, σ⟫_Prob` → `⟪↑ρ, ↑σ⟫_ℝ`
`↑p : ℝ` is the number inside `p : Prob`; on the right, `↑ρ` are the Hermitian matrices and `⟪·,·⟫_ℝ`
is their real inner product. -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) (P : ℝ → Prop)
    (h : P (inner ℝ ρ.M σ.M)) : P (inner Prob ρ σ : ℝ) := by
  rw [MState.val_inner]
  exact h

end purity

/-! ### R9. `HermitianMat.inner_eq_re_trace` · goal: `⟪A, B⟫_ℝ` → `RCLike.re (↑A * ↑B).trace`
`RCLike.re` is the real part on `ℝ` or `ℂ`; `M.trace` is `∑ i, M i i`. -/
example {d : Type} [Fintype d] (A B : HermitianMat d ℂ) (P : ℝ → Prop)
    (h : P (RCLike.re (A.mat * B.mat).trace)) : P (inner ℝ A B) := by
  rw [HermitianMat.inner_eq_re_trace]
  exact h

/-! ### R10. `rfl` · closes `RCLike.re z = z.re`: on `ℂ` the two real parts are the same by definition -/
example (z : ℂ) : RCLike.re z = z.re := by
  rfl

/-! ## Part 3 · Lagrange's identity (milestone `lagrange`) -/

/-! ### R11. `Complex.normSq_apply` · goal: `Complex.normSq z` → `z.re * z.re + z.im * z.im`
`Complex.normSq z = |z|²`, a real number. -/
example (z : ℂ) (P : ℝ → Prop) (h : P (z.re * z.re + z.im * z.im)) : P (Complex.normSq z) := by
  rw [Complex.normSq_apply]
  exact h

/-! ### R12. `Complex.add_re`, `add_im`, `sub_re`, `sub_im` · goal: real/imaginary part of `z ± w` -/
example (z w : ℂ) (P : ℝ → ℝ → Prop) (h : P (z.re + w.re) (z.im - w.im)) :
    P (z + w).re (z - w).im := by
  simp only [Complex.add_re, Complex.sub_im]
  exact h

/-! ### R13. `Complex.mul_re`, `Complex.mul_im` · goal: real/imaginary part of `z * w`
`(z w).re = z.re w.re − z.im w.im`, `(z w).im = z.re w.im + z.im w.re`. -/
example (z w : ℂ) (P : ℝ → ℝ → Prop)
    (h : P (z.re * w.re - z.im * w.im) (z.re * w.im + z.im * w.re)) : P (z * w).re (z * w).im := by
  simp only [Complex.mul_re, Complex.mul_im]
  exact h

/-! ### R14. `Complex.conj_re`, `Complex.conj_im` · goal: parts of `z̄`: `z̄.re = z.re`, `z̄.im = -z.im` -/
example (z : ℂ) (P : ℝ → ℝ → Prop) (h : P z.re (-z.im)) :
    P (starRingEnd ℂ z).re (starRingEnd ℂ z).im := by
  simp only [Complex.conj_re, Complex.conj_im]
  exact h

/-! ## Part 4 · The purity formula (`reduced_purity`) -/

/-! ### R15. `have hn := ψ.normalized` (`Ket.normalized`) · context gains `∑ x, Complex.normSq (ψ x) = 1`
`Ket d` is a unit vector in `ℂ^d`; `ψ x` is its amplitude at the basis state `x`. -/
example {d : Type} [Fintype d] (ψ : Ket d) (G : Prop) (k : ∑ x, Complex.normSq (ψ x) = 1 → G) :
    G := by
  have hn := ψ.normalized
  exact k hn

/-! ### R16. `simp only [Fintype.sum_prod_type] at hn` · context: a sum over `d₁ × d₂` → a double sum -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] (f : d₁ × d₂ → ℝ) (G : Prop)
    (k : ∑ x, ∑ y, f (x, y) = 1 → G) (hn : ∑ p, f p = 1) : G := by
  simp only [Fintype.sum_prod_type] at hn
  exact k hn

/-! ### R17. `Fin.sum_univ_two` · goal (or `at hn`): a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R18. `set x := e` · context gains `x : α := e`; every `e` in the goal and context becomes `x`
Later, `simp [x, …]` unfolds `x` again. -/
example {α : Type} (f : α → α) (a : α) (P : α → Prop) (h : P (f a)) : P (f a) := by
  set x := f a
  exact h

/-! ### R19. `Complex.mul_conj` · goal: `z * z̄` → `↑(Complex.normSq z)` (a real number cast into `ℂ`) -/
example (z : ℂ) (P : ℂ → Prop) (h : P (Complex.normSq z : ℂ)) : P (z * starRingEnd ℂ z) := by
  rw [Complex.mul_conj]
  exact h

/-! ### R20. `Matrix.trace_fin_two` · goal: `A.trace` → `A 0 0 + A 1 1` for a 2×2 matrix -/
example {α : Type} [AddCommMonoid α] (A : Matrix (Fin 2) (Fin 2) α) (P : α → Prop)
    (h : P (A 0 0 + A 1 1)) : P A.trace := by
  rw [Matrix.trace_fin_two]
  exact h

/-! ### R21. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index
`rw` rewrites the first product entry it finds; repeat it for the next one. -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R22. `rw [mul_comm a]` · goal: `a * b` → `b * a`, only for products whose left factor is `a`
With `a := starRingEnd ℂ _` it turns `z̄ * z` into `z * z̄`, the shape R19 needs. -/
example {α : Type} [CommMonoid α] (a b c : α) (P : α → α → Prop) (h : P (b * a) (c * b)) :
    P (a * b) (c * b) := by
  rw [mul_comm a]
  exact h

/-! ### R23. `Complex.ofReal_re`, `Complex.ofReal_im` · goal: parts of a real cast: `(↑r).re = r`, `(↑r).im = 0` -/
example (r : ℝ) (P : ℝ → ℝ → Prop) (h : P r 0) : P (r : ℂ).re (r : ℂ).im := by
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact h

/-! ### R24. `Complex.sq_norm` · goal: `‖z‖ ^ 2` → `Complex.normSq z`
`‖z‖` is the modulus `|z|` (a real number). -/
example (z : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z)) : P (‖z‖ ^ 2) := by
  rw [Complex.sq_norm]
  exact h

/-! ### R25. `linear_combination c₁ * h₁ + c₂ * h₂` · closes `lhs = rhs` when
`lhs − rhs − (c₁ (h₁.lhs − h₁.rhs) + c₂ (h₂.lhs − h₂.rhs))` is `0` by `ring`.
The coefficients `cᵢ` may be any expressions, not only numbers. -/
example (x y s : ℝ) (h₁ : x + y = s) (h₂ : x * y = 1) : x ^ 2 + y ^ 2 = s ^ 2 - 2 := by
  linear_combination (x + y + s) * h₁ - 2 * h₂

/-! ## Part 5 · Product state iff pure (`isProd_iff_reduced_pure`) -/

/-! ### R26. `Subtype.ext_iff` · goal: `p = q` in a subtype such as `Prob` → `↑p = ↑q` in `ℝ`
`Prob` is `{p : ℝ // 0 ≤ p ∧ p ≤ 1}`; two elements are equal iff their underlying numbers are. -/
example (p q : Prob) (P : Prop → Prop) (h : P ((p : ℝ) = q)) : P (p = q) := by
  rw [Subtype.ext_iff]
  exact h

/-! ### R27. `Prob.coe_one` · goal: `↑(1 : Prob)` → `(1 : ℝ)` -/
example (P : ℝ → Prop) (h : P 1) : P ((1 : Prob) : ℝ) := by
  rw [Prob.coe_one]
  exact h

/-! ### R28. `Ket.IsProd_iff_mul_eq_mul` · goal: `ψ.IsProd` → all 2×2 minors of `ψ` vanish
`ψ.IsProd` means `∃ ξ φ, ψ = ξ ⊗ᵠ φ` (a product state; `⊗ᵠ` is the tensor product of kets). -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] (ψ : Ket (d₁ × d₂)) (P : Prop → Prop)
    (h : P (∀ (i₁ i₂ : d₁) (j₁ j₂ : d₂), ψ (i₁, j₁) * ψ (i₂, j₂) = ψ (i₁, j₂) * ψ (i₂, j₁))) :
    P ψ.IsProd := by
  rw [Ket.IsProd_iff_mul_eq_mul]
  exact h

/-! ### R29. `rw [← sub_eq_zero (a := a)]` · goal: `a = b` → `a - b = 0`
`sub_eq_zero : a - b = 0 ↔ a = b`. Naming `a` makes `rw` rewrite only the equation with that left side. -/
example {α : Type} [AddGroup α] (a b c : α) (P : Prop → Prop → Prop) (h : P (a - b = 0) (c = b)) :
    P (a = b) (c = b) := by
  rw [← sub_eq_zero (a := a)]
  exact h

/-! ### R30. `rw [← norm_eq_zero]` · goal: `z = 0` → `‖z‖ = 0`
`norm_eq_zero : ‖z‖ = 0 ↔ z = 0`, for any normed group (`ℂ`, `ℝ`, vectors). -/
example (z : ℂ) (P : Prop → Prop) (h : P (‖z‖ = 0)) : P (z = 0) := by
  rw [← norm_eq_zero]
  exact h

/-! ### R31. `norm_nonneg` · the fact `0 ≤ ‖z‖` -/
example (z : ℂ) : 0 ≤ ‖z‖ := by
  exact norm_nonneg z

/-! ### R32. `nlinarith [t₁, …]` · closes a polynomial (in)equality over `ℝ` from the hypotheses and
the extra facts `tᵢ`, by multiplying pairs of them. Here: `1 − 2a² = 1` and `0 ≤ a` give `a = 0`. -/
example (a : ℝ) (h : 1 - 2 * a ^ 2 = 1) (ha : 0 ≤ a) : a = 0 := by
  nlinarith [ha]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Normalisation of a one-qubit ket, split into its two terms: R15, R17 -/
example (φ : Ket (Fin 2)) : Complex.normSq (φ 0) + Complex.normSq (φ 1) = 1 := by
  have hn := φ.normalized
  rw [Fin.sum_univ_two] at hn
  exact hn

/-! ### W2. A complex identity reduced to real parts: R11, R13, then `ring` -/
example (z w : ℂ) : Complex.normSq (z * w) = Complex.normSq z * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-! ### W3. The trace of a square of a 2×2 matrix: R20, R21, R17 -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * A).trace = A 0 0 * A 0 0 + A 0 1 * A 1 0 + (A 1 0 * A 0 1 + A 1 1 * A 1 1) := by
  rw [Matrix.trace_fin_two]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]

/-! ### W4. A norm equation → a vanishing number: R29, R30, R31, R32 -/
example (z w : ℂ) : 3 + ‖z - w‖ ^ 2 = 3 ↔ z = w := by
  rw [← sub_eq_zero (a := z)]
  rw [← norm_eq_zero]
  constructor
  · intro h
    nlinarith [norm_nonneg (z - w)]
  · intro h
    rw [h]
    ring

/-! ### W5. All index combinations: `fin_cases` on each index, then `simp [h, mul_comm]` -/
example (g : Fin 2 → ℂ) (h : g 0 * g 1 = 2) : ∀ i j : Fin 2, i ≠ j → g i * g j = 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h, mul_comm]

end H078Guide

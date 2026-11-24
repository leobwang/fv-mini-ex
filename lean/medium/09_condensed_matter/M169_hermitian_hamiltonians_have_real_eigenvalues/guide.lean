/- Guide for M169 (Hermitian Hamiltonians have real eigenvalues).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal (or hypothesis)": the step changes only the part shown inside
`P (…)`. A hypothesis `h` or `g` in an entry is only there to finish the example.
`V` is any complex inner product space (`[NormedAddCommGroup V] [InnerProductSpace ℂ V]`);
`T.HilbertSpace` is one of them.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace M169Guide

/-! # Part R · Reference entries -/

/-! ## Getting an equation to work on -/

/-! ### R1. `have h := T.hamiltonian_hermitian ψ φ` · context gains the hermiticity equation
`TightBindingChain.hamiltonian_hermitian : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ`.
`T.hamiltonian_hermitian ψ φ` is that lemma with `T`, `ψ`, `φ` filled in (dot notation supplies `T`).
With no `: type`, `have` takes the type of the right-hand side. -/
example (T : TightBindingChain) (ψ φ : T.HilbertSpace) (G : Prop)
    (g : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ → G) : G := by
  have h := T.hamiltonian_hermitian ψ φ
  exact g h

/-! ### R2. `rw [hab] at h` · context: hypothesis `h` rewritten; goal unchanged -/
example {α : Type} (a b : α) (P : α → Prop) (G : Prop) (hab : a = b) (h : P a)
    (g : P b → G) : G := by
  rw [hab] at h
  exact g h

/-! ## Pulling scalars out of the inner product -/

/-! ### R3. `inner_smul_left` · `⟪r • x, y⟫_ℂ = (starRingEnd ℂ) r * ⟪x, y⟫_ℂ` · goal
A scalar leaves the FIRST slot conjugated: `(starRingEnd ℂ) r` is `conj r`.
Shown on the goal; `rw [inner_smul_left] at h` does the same inside a hypothesis (R2). -/
example {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x y : V) (r : ℂ)
    (P : ℂ → Prop) (h : P ((starRingEnd ℂ) r * ⟪x, y⟫_ℂ)) : P ⟪r • x, y⟫_ℂ := by
  rw [inner_smul_left]
  exact h

/-! ### R4. `inner_smul_right` · `⟪x, r • y⟫_ℂ = r * ⟪x, y⟫_ℂ` · goal
A scalar leaves the SECOND slot unchanged. Also works `at h`. -/
example {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x y : V) (r : ℂ)
    (P : ℂ → Prop) (h : P (r * ⟪x, y⟫_ℂ)) : P ⟪x, r • y⟫_ℂ := by
  rw [inner_smul_right]
  exact h

/-! ## Cancelling and reading off realness -/

/-! ### R5. `inner_self_ne_zero` · `⟪x, x⟫_ℂ ≠ 0 ↔ x ≠ 0` · goal `⟪x, x⟫_ℂ ≠ 0` → `x ≠ 0`
`rw` accepts an `↔` and rewrites one proposition into the other. As a term:
`inner_self_ne_zero.mpr hx : ⟪x, x⟫_ℂ ≠ 0` from `hx : x ≠ 0`. -/
example {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : V) (hx : x ≠ 0) :
    ⟪x, x⟫_ℂ ≠ 0 := by
  rw [inner_self_ne_zero]
  exact hx

/-! ### R6. `mul_right_cancel₀` · `b ≠ 0 → a * b = c * b → a = c` · goal `a = c` → `a * b = c * b`
The lemma asks for `[Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀]`; every field (`ℂ`, `ℝ`) has them. -/
example {K : Type} [Field K] (a b c : K) (hb : b ≠ 0) (h : a * b = c * b) :
    a = c := by
  apply mul_right_cancel₀ hb
  exact h

/-! ### R7. `Complex.conj_eq_iff_im` · `(starRingEnd ℂ) z = z ↔ z.im = 0`
Right to left: goal `z.im = 0` → `(starRingEnd ℂ) z = z`. -/
example (z : ℂ) (h : (starRingEnd ℂ) z = z) : z.im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Substitute a vector, then pull both scalars out: R2 → R3 → R4 on one hypothesis -/
example {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x y : V) (c : ℂ)
    (hx : x = c • y) (h : ⟪x, x⟫_ℂ = 1) : (starRingEnd ℂ) c * (c * ⟪y, y⟫_ℂ) = 1 := by
  rw [hx] at h
  rw [inner_smul_left] at h
  rw [inner_smul_right] at h
  exact h

/-! ### W2. Cancel a nonzero `⟪y, y⟫_ℂ`: R6 with the side fact from R5 -/
example {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (y : V) (hy : y ≠ 0) (a : ℂ)
    (h : a * ⟪y, y⟫_ℂ = 2 * ⟪y, y⟫_ℂ) : a = 2 := by
  have hn : ⟪y, y⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hy
  apply mul_right_cancel₀ hn
  exact h

/-! ### W3. A real number cast into `ℂ` has imaginary part `0`: R7, then `Complex.conj_ofReal`
(`Complex.conj_ofReal r : (starRingEnd ℂ) ↑r = ↑r`). -/
example (r : ℝ) : (r : ℂ).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  exact Complex.conj_ofReal r

end M169Guide

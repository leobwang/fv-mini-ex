/- Guide for E121 (Energy expectation values are real).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. A hypothesis `h` or `g` in an entry is only there to finish the example; it shows
what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (an arbitrary vector `x`, an
arbitrary linear map `A`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace E121Guide

/-! # Part R · Reference entries -/

/-! ## The physics input: hermiticity -/

/-! ### R1. `T.hamiltonian_hermitian ψ φ` · context gains `h : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ`
`CondensedMatter.TightBindingChain.hamiltonian_hermitian (T) (ψ φ : T.HilbertSpace)`; with
`T : TightBindingChain` the dot notation `T.hamiltonian_hermitian` fills `T`. You choose `ψ` and `φ`. -/
example (T : TightBindingChain) (ψ φ : T.HilbertSpace) (G : Prop)
    (g : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ → G) : G := by
  have h := T.hamiltonian_hermitian ψ φ
  exact g h

/-! ## Conjugate symmetry of the inner product -/

/-! ### R2. `inner_conj_symm` · `conj ⟪y, x⟫ = ⟪x, y⟫`; `rw [← inner_conj_symm]` · goal (or `at h`: context)
Right to left it turns `⟪x, y⟫_ℂ` into `(starRingEnd ℂ) ⟪y, x⟫_ℂ`, the conjugate of the swapped
product. `(starRingEnd ℂ) z` is how Lean prints the complex conjugate `conj z`. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (P : ℂ → Prop)
    (h : P ((starRingEnd ℂ) ⟪y, x⟫_ℂ)) : P ⟪x, y⟫_ℂ := by
  rw [← inner_conj_symm]
  exact h

/-- The same rewrite inside a hypothesis: `at h` changes `h`, the goal stays. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (P : ℂ → Prop)
    (h : P ⟪x, y⟫_ℂ) : P ((starRingEnd ℂ) ⟪y, x⟫_ℂ) := by
  rw [← inner_conj_symm] at h
  exact h

/-! ## A complex number equal to its conjugate is real -/

/-! ### R3. `Complex.conj_eq_iff_im` · `conj z = z ↔ z.im = 0`; `exact Complex.conj_eq_iff_im.mp h` · closes the goal
`.mp` is the `→` direction of the `↔` (E005); `.mpr` is `←`. `z.im : ℝ` is the imaginary part. -/
example (z : ℂ) (h : (starRingEnd ℂ) z = z) : z.im = 0 := by
  exact Complex.conj_eq_iff_im.mp h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `⟪x, x⟫_ℂ` is real: R2 used forward as a `have`, then R3
`inner_conj_symm x x : conj ⟪x, x⟫ = ⟪x, x⟫` already has the shape R3 needs; no rewrite is required.
`(𝕜 := ℂ)` names the scalar field, which Lean cannot guess from `x x` alone. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) : (⟪x, x⟫_ℂ).im = 0 := by
  have h := inner_conj_symm (𝕜 := ℂ) x x
  exact Complex.conj_eq_iff_im.mp h

/-! ### W2. `rw [← inner_conj_symm]` on an equation rewrites only the FIRST inner product it meets
It fixes `x, y` from the first match (`⟪A x, y⟫`) and rewrites that term only; the right side stays. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : E →ₗ[ℂ] E) (x y : E)
    (h : (starRingEnd ℂ) ⟪y, A x⟫_ℂ = ⟪x, A y⟫_ℂ) : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  rw [← inner_conj_symm]
  exact h

end E121Guide

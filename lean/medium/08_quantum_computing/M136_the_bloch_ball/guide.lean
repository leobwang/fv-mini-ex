/- Guide for M136 (The Bloch ball).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. `G` is a goal the step does not touch; a hypothesis `k` in an entry is only there to
finish the example.
Part W: worked combinations on objects that are NOT the exercise's (qutrit states, `Fin 3`).
Assumed: Lean basics (E001–E033). New: physlib's `MState`, Mathlib's `Matrix`, `ℂ` with `re`/`im`,
`star`, and the order `≤` on `ℂ` from `open scoped ComplexOrder`.
-/
import QuantumInfo.States.Mixed.MState

open scoped ComplexOrder

namespace M136Guide

/-! # Part R · Reference entries -/

/-! ## The three facts every state carries -/

/-! ### R1. `ρ.psd` (`MState.psd`) · context gains `h : ρ.m.PosSemidef`
`ρ.m : Matrix d d ℂ` is the density matrix of the state `ρ`. -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (G : Prop)
    (k : ρ.m.PosSemidef → G) : G := by
  have h := ρ.psd
  exact k h

/-! ### R2. `Matrix.PosSemidef.det_nonneg` · `A.PosSemidef → 0 ≤ A.det` · context gains `0 ≤ A.det`
The `≤` here is on `ℂ` (see `Complex.nonneg_iff`, R12). Dot notation: `hA.det_nonneg`. -/
example {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosSemidef) (G : Prop)
    (k : 0 ≤ A.det → G) : G := by
  have hdet := hA.det_nonneg
  exact k hdet

/-! ### R3. `ρ.tr'` (`MState.tr'`) · context gains `htr : ρ.m.trace = 1` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (G : Prop)
    (k : ρ.m.trace = 1 → G) : G := by
  have htr := ρ.tr'
  exact k htr

/-! ### R4. `ρ.Hermitian` (`MState.Hermitian`) · context gains `h : ρ.m.IsHermitian` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (G : Prop)
    (k : ρ.m.IsHermitian → G) : G := by
  have h := ρ.Hermitian
  exact k h

/-! ## Hermitian entries -/

/-! ### R5. `Matrix.IsHermitian.apply` · `A.IsHermitian → star (A j i) = A i j` · context gains one entry equation -/
example {n : Type} (A : Matrix n n ℂ) (hA : A.IsHermitian) (i j : n) (G : Prop)
    (k : star (A j i) = A i j → G) : G := by
  have h := hA.apply i j
  exact k h

/-! ### R6. `h.symm` · from `h : a = b` get `b = a` -/
example {α : Type} (a b : α) (h : a = b) (G : Prop) (k : b = a → G) : G := by
  have h' := h.symm
  exact k h'

/-! ### R7. `congrArg Complex.im h` · from `h : z = w` get `z.im = w.im` (same with `Complex.re`) -/
example (z w : ℂ) (h : z = w) (G : Prop) (k : z.im = w.im → G) : G := by
  have h' := congrArg Complex.im h
  exact k h'

/-! ### R8. `simp at h` with `RCLike.star_def`, `Complex.conj_im` · `(star z).im` → `-z.im`
On `ℂ`, `star z` is the complex conjugate. -/
example (z : ℂ) (G : Prop) (h : (star z).im = z.im) (k : -z.im = z.im → G) : G := by
  simp at h
  exact k h

/-! ### R9. `linarith` · closes a goal that follows linearly from hypotheses (over `ℝ`, `ℚ`, …) -/
example (a : ℝ) (h : -a = a) : a = 0 := by
  linarith

/-! ## Determinant and trace of a 2×2 matrix -/

/-! ### R10. `rw [Matrix.det_fin_two] at h` · `A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0` · context -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ → Prop) (h : P A.det) (G : Prop)
    (k : P (A 0 0 * A 1 1 - A 0 1 * A 1 0) → G) : G := by
  rw [Matrix.det_fin_two] at h
  exact k h

/-! ### R11. `rw [e] at h` · rewrite inside a hypothesis with an equation `e : a = b` -/
example {α : Type} (a b : α) (P : α → Prop) (e : a = b) (h : P a) (G : Prop) (k : P b → G) : G := by
  rw [e] at h
  exact k h

/-! ### R12. `Complex.nonneg_iff` · `0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im` · context
Needs `open scoped ComplexOrder`: `0 ≤ z` on `ℂ` means "real and nonnegative". -/
example (z : ℂ) (h : 0 ≤ z) (G : Prop) (k : 0 ≤ z.re ∧ 0 = z.im → G) : G := by
  rw [Complex.nonneg_iff] at h
  exact k h

/-! ### R13. `rw [Matrix.trace_fin_two] at h` · `A.trace = A 0 0 + A 1 1` · context -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ → Prop) (h : P A.trace) (G : Prop)
    (k : P (A 0 0 + A 1 1) → G) : G := by
  rw [Matrix.trace_fin_two] at h
  exact k h

/-! ## Real parts -/

/-! ### R14. `simp at h` with `Complex.add_re`, `Complex.one_re` · real part of a sum, of `1` -/
example (z w : ℂ) (h : (z + w).re = Complex.re 1) (G : Prop) (k : z.re + w.re = 1 → G) : G := by
  simp at h
  exact k h

/-! ### R15. `Complex.mul_re` · `(z * w).re = z.re * w.re - z.im * w.im`
With `w` conjugated, `simp` finishes with `Complex.conj_re`, `Complex.conj_im`. -/
example (z w : ℂ) (P : ℝ → Prop) (h : P (z * star w).re) (G : Prop)
    (k : P (z.re * w.re + z.im * w.im) → G) : G := by
  rw [Complex.mul_re] at h
  simp at h
  exact k h

/-! ### R16. `simp at h` with `sub_nonneg` · `0 ≤ a - b` → `b ≤ a` -/
example (a b : ℝ) (h : 0 ≤ a - b) (G : Prop) (k : b ≤ a → G) : G := by
  simp at h
  exact k h

/-! ### R17. `simp [h₀] at h₁ h₂` · several hypotheses at once, using `h₀` as a rewrite rule
Simplified hypotheses move to the end of the context. -/
example (z w : ℂ) (P : ℝ → Prop) (h₀ : z.im = 0) (h₁ : P (z * w).re) (h₂ : P (z * w).im) (G : Prop)
    (k : P (z.re * w.re) → P (z.re * w.im) → G) : G := by
  simp [h₀] at h₁ h₂
  exact k h₁ h₂

/-! ## Closing -/

/-- A definition on states that is not the exercise's: the real part of entry `(1, 1)`. -/
def pop1 (ρ : MState (Fin 2)) : ℝ := (ρ.m 1 1).re

/-! ### R18. `simp only [D]` · goal: a defined name → its body -/
example (ρ : MState (Fin 2)) (P : ℝ → Prop) (h : P (ρ.m 1 1).re) : P (pop1 ρ) := by
  simp only [pop1]
  exact h

/-! ### R19. `nlinarith [t₁, h.1]` · closes a goal of real polynomial (in)equalities
It multiplies pairs of hypotheses and of the extra terms `tᵢ`; `h.1` is the left half of `h : A ∧ B`. -/
example (a b : ℝ) (h : 0 ≤ a * b ∧ 0 ≤ b) : (a - b) ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [h.1]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Trace of a qutrit state, in real parts: R3, `Matrix.trace_fin_three`, R7, R14 -/
example (ρ : MState (Fin 3)) : (ρ.m 0 0).re + (ρ.m 1 1).re + (ρ.m 2 2).re = 1 := by
  have htr := ρ.tr'
  rw [Matrix.trace_fin_three] at htr
  have htr' := congrArg Complex.re htr
  simp at htr'
  exact htr'

/-! ### W2. A diagonal entry of a qutrit state is real: R4, R5, R7, R8, R9 -/
example (ρ : MState (Fin 3)) : (ρ.m 2 2).im = 0 := by
  have h := congrArg Complex.im (ρ.Hermitian.apply 2 2)
  simp at h
  linarith

/-! ### W3. `nlinarith` with a square as a hint: `sq_nonneg t : 0 ≤ t ^ 2` -/
example (a b : ℝ) (h : a + b = 1) : a * b ≤ 1 / 4 := by
  nlinarith [sq_nonneg (a - b)]

end M136Guide

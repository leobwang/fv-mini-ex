/- Guide for M127 (Z-rotations and the 2π sign).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a phase gate, `π / 2`, `t / 3`).
Assumed: Lean basics (E001–E033). `cexp` is notation for `Complex.exp`; `I` is `Complex.I`;
`starRingEnd ℂ` is complex conjugation.
-/
import Mathlib

open Matrix Complex

namespace M127Guide

/-! # Part R · Reference entries -/

/-! ## Products of diagonal matrices and exponentials -/

/-! ### R1. Unfold a definition with an argument: `simp only [D]` (or `rw [D]`) · goal: `D t` → its body -/
noncomputable def D (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(t : ℂ), 0; 0, 1]

example (t : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P !![(t : ℂ), 0; 0, 1]) : P (D t) := by
  simp only [D]
  exact h

example (t : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P !![(t : ℂ), 0; 0, 1]) : P (D t) := by
  rw [D]
  exact h

/-! ### R2. `Matrix.mul_fin_two` · goal: product of two `!![…]` literals → one literal of sums -/
example {α : Type} [AddCommMonoid α] [Mul α] (a b c d p q r s : α)
    (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]) :
    P (!![a, b; c, d] * !![p, q; r, s]) := by
  rw [Matrix.mul_fin_two]
  exact h

/-! ### R3. `Complex.exp_add` · `cexp (x + y) = cexp x * cexp y`; right to left merges a product -/
example (x y : ℂ) (P : ℂ → Prop) (h : P (cexp (x + y))) : P (cexp x * cexp y) := by
  rw [← Complex.exp_add]
  exact h

/-! ### R4. `push_cast` · goal: moves the cast `ℝ → ℂ` inward (`Complex.ofReal_add`, `ofReal_mul`, …) -/
example (r s : ℝ) (P : ℂ → Prop) (h : P ((r : ℂ) + (s : ℂ))) : P ((r + s : ℝ) : ℂ) := by
  push_cast
  exact h

example (r : ℝ) (P : ℂ → Prop) (h : P (2 * (r : ℂ))) : P ((2 * r : ℝ) : ℂ) := by
  push_cast
  exact h

/-! ### R5. `ring_nf` · normalises every ring subterm, also inside `cexp` and `!![…]`; closes the goal
when both sides reach the same normal form -/
example (f : ℂ → ℂ) (x y : ℂ) : f (x / 2 + y / 2) + 0 * 0 = f ((x + y) / 2) := by
  ring_nf

/-! ## The full turn -/

/-! ### R6. `Matrix.one_fin_two` · goal: the identity `1` → the literal `!![1, 0; 0, 1]` -/
example {α : Type} [Zero α] [One α] (P : Matrix (Fin 2) (Fin 2) α → Prop) (h : P !![1, 0; 0, 1]) :
    P 1 := by
  rw [Matrix.one_fin_two]
  exact h

/-! ### R7. `rw [show x = y by ring]` · goal: rewrite a subterm into the shape a lemma needs -/
example (a : ℂ) (P : ℂ → Prop) (h : P (a * I)) : P (2 * a / 2 * I) := by
  rw [show 2 * a / 2 * I = a * I by ring]
  exact h

/-! ### R8. `Complex.exp_neg` · `cexp (-x) = (cexp x)⁻¹` -/
example (x : ℂ) (P : ℂ → Prop) (h : P (cexp x)⁻¹) : P (cexp (-x)) := by
  rw [Complex.exp_neg]
  exact h

/-! ### R9. `Complex.exp_pi_mul_I` · `cexp (↑Real.pi * I) = -1` (Euler) -/
example (P : ℂ → Prop) (h : P (-1)) : P (cexp (↑Real.pi * I)) := by
  rw [Complex.exp_pi_mul_I]
  exact h

/-! ### R10. `simp` on an entry of `-!![…]` (`Matrix.neg_apply`, `Matrix.of_apply`, `cons_val_…`) · goal -/
example {α : Type} [Neg α] (a b c d : α) (P : α → Prop) (h : P (-b)) :
    P ((-!![a, b; c, d]) 0 1) := by
  simp
  exact h

/-! ## Unitarity and conjugation -/

/-! ### R11. `Matrix.mem_unitaryGroup_iff` · goal: membership → an equation -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M * star M = 1) : M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact h

/-! ### R12. `Matrix.star_eq_conjTranspose` · goal: `star M` → `Mᴴ` (conjugate transpose) -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P Mᴴ) :
    P (star M) := by
  rw [Matrix.star_eq_conjTranspose]
  exact h

/-! ### R13. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R14. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R15. `Matrix.conjTranspose_apply` · goal: entry `(i, j)` of `Mᴴ` → `star` of entry `(j, i)` -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (P : ℂ → Prop) (h : P (star (M j i))) :
    P (Mᴴ i j) := by
  rw [Matrix.conjTranspose_apply]
  exact h

/-! ### R16. `Complex.exp_conj` · `cexp (conj x) = conj (cexp x)`; right to left moves `conj` inside -/
example (x : ℂ) (P : ℂ → Prop) (h : P (cexp ((starRingEnd ℂ) x))) :
    P ((starRingEnd ℂ) (cexp x)) := by
  rw [← Complex.exp_conj]
  exact h

/-! ### R17. `map_neg`, `map_mul`, `map_div₀` · goal: `conj` distributes over `-`, `*`, `/` -/
example (x y z : ℂ) (P : ℂ → Prop)
    (h : P (-((starRingEnd ℂ) x / (starRingEnd ℂ) y * (starRingEnd ℂ) z))) :
    P ((starRingEnd ℂ) (-(x / y * z))) := by
  simp only [map_neg, map_mul, map_div₀]
  exact h

/-! ### R18. `Complex.conj_ofReal`, `Complex.conj_I` · goal: `conj ↑r = ↑r`, `conj I = -I` -/
example (r : ℝ) (P : ℂ → Prop) (h : P (↑r * -I)) : P ((starRingEnd ℂ) ↑r * (starRingEnd ℂ) I) := by
  simp only [Complex.conj_ofReal, Complex.conj_I]
  exact h

/-! ### R19. `map_ofNat` · goal: `conj 2` → `2` (a numeral literal is fixed by every ring map)
`simp` does not do this by itself: name it, or it stops at `(starRingEnd ℂ) 2` (W3). -/
example (P : ℂ → Prop) (h : P 2) : P ((starRingEnd ℂ) 2) := by
  simp only [map_ofNat]
  exact h

/-! ### R20. `neg_add_cancel` · `-a + a = 0` (and `add_neg_cancel` · `a + -a = 0`) -/
example {α : Type} [AddGroup α] (a : α) (P : α → Prop) (h : P 0) : P (-a + a) := by
  rw [neg_add_cancel]
  exact h

/-! ### R21. `Complex.exp_zero` · `cexp 0 = 1` -/
example (P : ℂ → Prop) (h : P 1) : P (cexp 0) := by
  rw [Complex.exp_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A phase gate composes additively: R1, R2, R3, R4, R5 -/
noncomputable def Ph (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, cexp ((φ : ℂ) * I)]

example (a b : ℝ) : Ph a * Ph b = Ph (a + b) := by
  simp only [Ph, Matrix.mul_fin_two, ← Complex.exp_add]
  push_cast
  ring_nf

/-! ### W2. Two quarter turns of the phase: R3, R7, R9 -/
example : cexp (↑Real.pi / 2 * I) * cexp (↑Real.pi / 2 * I) = -1 := by
  rw [← Complex.exp_add]
  rw [show (↑Real.pi / 2 * I + ↑Real.pi / 2 * I : ℂ) = ↑Real.pi * I by ring]
  rw [Complex.exp_pi_mul_I]

/-! ### W3. `|e^{it/3}|² = 1`: without `map_ofNat`, `simp` stops at `conj 3` -/
example (t : ℝ) : cexp (↑t / 3 * I) * (starRingEnd ℂ) (cexp (↑t / 3 * I)) = 1 := by
  simp [← Complex.exp_conj]
  simp [map_ofNat, ← Complex.exp_add]

end M127Guide

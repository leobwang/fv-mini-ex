/- Guide for E113 (Density matrix of a pure state).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (plain complex numbers and vectors).
Assumed: Lean basics (E001–E033); E112 (kets) helps but is not needed.
-/
import QuantumInfo.States.Mixed.MState

open ComplexConjugate

namespace E113Guide

/-! # Part R · Reference entries -/

/-! ## Entries of a pure state's density matrix -/

/-! ### R1. `MState.pure_apply` · goal: entry `(MState.pure ψ).m i j` → `ψ i * conj (ψ j)`
`MState.pure ψ : MState d` is the density matrix |ψ⟩⟨ψ|; `.m` is its raw matrix `Matrix d d ℂ`, and
`ψ i : ℂ` is entry `i` of the ket. `conj z` prints as `(starRingEnd ℂ) z`. The indices `i j` are
implicit in the lemma, so `rw` finds them in the goal; each `rw` rewrites one entry pattern. -/
example {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (a b : d) (P : ℂ → Prop)
    (h : P (ψ a * conj (ψ b))) : P ((MState.pure ψ).m a b) := by
  rw [MState.pure_apply]
  exact h

/-! ## Conjugation algebra -/

/-! ### R2. `map_mul` · goal: `conj (a * b)` → `conj a * conj b`
`map_mul f x y : f (x * y) = f x * f y` holds for every multiplicative map `f`; `conj` is one. -/
example (a b : ℂ) (P : ℂ → Prop) (h : P (conj a * conj b)) : P (conj (a * b)) := by
  rw [map_mul]
  exact h

/-! ### R3. `Complex.conj_conj` · goal: `conj (conj a)` → `a` -/
example (a : ℂ) (P : ℂ → Prop) (h : P a) : P (conj (conj a)) := by
  rw [Complex.conj_conj]
  exact h

/-! ### R4. `mul_comm` · goal: `a * b` → `b * a`
With no arguments, `rw [mul_comm]` rewrites the FIRST product it meets (reading the goal left to
right) and every other copy of that same product. `rw [mul_comm a]` picks the product starting with `a`. -/
example {α : Type} [CommMonoid α] (a b : α) (P : α → Prop) (h : P (b * a)) : P (a * b) := by
  rw [mul_comm]
  exact h

/-! ### R5. `Complex.mul_conj` · goal: `z * conj z` → `↑(Complex.normSq z)`
`Complex.normSq z = re z ^ 2 + im z ^ 2 = |z|²` is a REAL number (`ℝ`); `↑` casts it back into `ℂ`. -/
example (z : ℂ) (P : ℂ → Prop) (h : P ↑(Complex.normSq z)) : P (z * conj z) := by
  rw [Complex.mul_conj]
  exact h

/-! ## Sums and casts -/

/-! ### R6. `simp only [lemma]` under `∑` · goal: rewrites inside the summand
`∑ x, f x` is `Finset.sum Finset.univ (fun x => f x)`: the summand sits under a binder `x`, where
`rw` cannot reach: it fails with "Did not find an occurrence of the pattern". `simp only`
rewrites under binders, at every `x` at once. -/
example {d : Type} [Fintype d] (v : d → ℂ) (P : ℂ → Prop)
    (h : P (∑ x, ↑(Complex.normSq (v x)))) : P (∑ x, v x * conj (v x)) := by
  simp only [Complex.mul_conj]
  exact h

/-! ### R7. `Ket.normalized` · context gains `∑ x, Complex.normSq (ψ x) = 1` (an equation in `ℝ`)
`Ket d` is a structure: a vector `vec : d → ℂ` with a proof `normalized'` that its norms squared
sum to 1. `ψ.normalized` restates that proof with `Complex.normSq`. -/
example {d : Type} [Fintype d] (ψ : Ket d) (G : Prop)
    (g : ∑ x, Complex.normSq (ψ x) = 1 → G) : G := by
  have hψ := ψ.normalized
  exact g hψ

/-! ### R8. `exact_mod_cast h` · closes a goal that is `h` up to casts
Here the goal lives in `ℂ` with each summand cast from `ℝ`; `h` lives in `ℝ`. `exact_mod_cast`
moves casts outward on both sides (`∑ x, ↑(f x)` → `↑(∑ x, f x)`, `1` → `↑1`), drops the cast with
`↑a = ↑b ↔ a = b`, then uses `h`. `norm_cast` does the first part alone (W3). -/
example {d : Type} [Fintype d] (f : d → ℝ) (hf : ∑ x, f x = 1) : ∑ x, (f x : ℂ) = 1 := by
  exact_mod_cast hf

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Conjugating a product whose FIRST factor is a conjugate: R2, R3, R4 -/
example (a b : ℂ) : conj (conj a * b) = conj b * a := by
  rw [map_mul]
  rw [Complex.conj_conj]
  rw [mul_comm]

/-! ### W2. A sum of `v x * conj (v x)` from a real sum: R6, then R8 -/
example {d : Type} [Fintype d] (v : d → ℂ) (hv : ∑ x, Complex.normSq (v x) = 2) :
    ∑ x, v x * conj (v x) = 2 := by
  simp only [Complex.mul_conj]
  exact_mod_cast hv

/-! ### W3. What `exact_mod_cast` does first: `norm_cast` pulls the cast out of the sum and drops it
(`hf` is stated the other way round here, so `norm_cast` cannot close the goal with it by itself). -/
example {d : Type} [Fintype d] (f : d → ℝ) (hf : 3 = ∑ x, f x) : ∑ x, (f x : ℂ) = 3 := by
  norm_cast
  exact hf.symm

end E113Guide

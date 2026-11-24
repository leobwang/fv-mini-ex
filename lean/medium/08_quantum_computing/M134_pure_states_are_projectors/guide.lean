/- Guide for M134 (Pure states are projectors).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a ket times another matrix,
a vector of squared norm 2, constants around a sum).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Mixed.MState

namespace M134Guide

/-! # Part R · Reference entries -/

/-! ## Matrix equation → one entry, then evaluate the entry -/

/-! ### R1. `ext i j` (lemma `Matrix.ext`) · goal `M = N` → context gains `i j : d`, goal is entry `(i, j)`
`d` is any finite index type here, not just `Fin 2`, so there is no `fin_cases` afterwards. -/
example {d α : Type} (M N : Matrix d d α) (h : ∀ i j, M i j = N i j) : M = N := by
  ext i j
  exact h i j

/-! ### R2. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {d α : Type} [Fintype d] [Mul α] [AddCommMonoid α] (M N : Matrix d d α) (i k : d)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R3. `simp only [MState.pure_apply]` · goal: entry of `(MState.pure φ).m` → `φ i * conj (φ j)`
The entries sit inside `∑ k, …`, under the binder `k`, where `rw` cannot reach; `simp only` can. -/
example {d : Type} [Fintype d] [DecidableEq d] (φ : Ket d) (A : Matrix d d ℂ) (i j : d)
    (P : ℂ → Prop) (h : P (∑ k, φ i * (starRingEnd ℂ) (φ k) * A k j)) :
    P (∑ k, (MState.pure φ).m i k * A k j) := by
  simp only [MState.pure_apply]
  exact h

/-! ## Normalisation: from `∑ ‖φ x‖² = 1` in `ℝ` to `∑ conj (φ x) * φ x = 1` in `ℂ` -/

/-! ### R4. `have := φ.normalized'` (field `Ket.normalized'`) · context gains `this : ∑ x, ‖φ.vec x‖ ^ 2 = 1`
`φ.vec x` and `φ x` are the same amplitude: `φ x` is the coercion of `φ` to a function, which unfolds
to `φ.vec x` (`Ket.coe_fun_eq`). -/
example {d : Type} [Fintype d] (φ : Ket d) (G : Prop) (g : (∑ x, ‖φ.vec x‖ ^ 2 = 1) → G) : G := by
  have := φ.normalized'
  exact g this

/-! ### R5. `simp only [Complex.conj_mul']` · goal: `conj z * z` → `↑‖z‖ ^ 2`, also under `∑` -/
example {d : Type} [Fintype d] (f : d → ℂ) (P : ℂ → Prop) (h : P (∑ k, (‖f k‖ : ℂ) ^ 2)) :
    P (∑ k, (starRingEnd ℂ) (f k) * f k) := by
  simp only [Complex.conj_mul']
  exact h

/-! ### R6. `exact_mod_cast h` · closes a goal in `ℂ` built from casts `↑r` of reals, from the same
statement `h` in `ℝ`. It moves the casts outward (`↑a ^ 2 = ↑(a ^ 2)`, `∑ ↑ = ↑∑`, `↑1 = 1`) on both. -/
example {d : Type} [Fintype d] (r : d → ℝ) (c : ℝ) (h : ∑ x, r x ^ 2 = c) :
    ∑ x, (r x : ℂ) ^ 2 = c := by
  exact_mod_cast h

/-! ## Chaining equations and moving factors through `∑` -/

/-! ### R7. `calc` · goal `a = c` → one goal per step `a = b`, `b = c`
Each step is `_ = t := proof`; `?_` leaves the proof as a new goal. -/
example {α : Type} (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  calc a = b := ?_
    _ = c := ?_
  exacts [h₁, h₂]

/-! ### R8. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal: factor on the left moves in -/
example {d R : Type} [Fintype d] [NonUnitalNonAssocSemiring R] (a : R) (f : d → R) (P : R → Prop)
    (h : P (∑ k, a * f k)) : P (a * ∑ k, f k) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R9. `Finset.sum_mul` · `(∑ i ∈ s, f i) * b = ∑ i ∈ s, f i * b` · goal: factor on the right moves in -/
example {d R : Type} [Fintype d] [NonUnitalNonAssocSemiring R] (b : R) (f : d → R) (P : R → Prop)
    (h : P (∑ k, f k * b)) : P ((∑ k, f k) * b) := by
  rw [Finset.sum_mul]
  exact h

/-! ### R10. `congr 1` · goal `∑ k, F k = ∑ k, G k` → goal `(fun k => F k) = fun k => G k` -/
example {d R : Type} [Fintype d] [CommRing R] (a : R) (f : d → R)
    (h : ∀ k, a * f k = f k * a) : ∑ k, a * f k = ∑ k, f k * a := by
  congr 1
  exact funext h

/-! ### R11. `ext k` (lemma `funext`) · goal `(fun k => F k) = fun k => G k` → context gains `k`, goal `F k = G k` -/
example {d R : Type} [CommRing R] (a : R) (f : d → R) (h : ∀ k, a * f k = f k * a) :
    (fun k => a * f k) = fun k => f k * a := by
  ext k
  exact h k

/-! ### R12. `ring` · closes an identity of commutative rings; `(starRingEnd ℂ) w` is just an unknown to it -/
example (a b w : ℂ) : a * (starRingEnd ℂ) w * b = (starRingEnd ℂ) w * (b * a) := by ring

/-! ### R13. `mul_one` · `a * 1 = a` · goal: drop a factor `1` (after `rw [h]` with `h : … = 1`) -/
example {M : Type} [MulOneClass M] (a b : M) (P : M → Prop) (h : P (a * b)) : P (a * 1 * b) := by
  rw [mul_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A pure state times another matrix `A`, entry `(i, j)`: R2, R3 → R8 → R10 → R11 → R12 -/
example {d : Type} [Fintype d] [DecidableEq d] (φ : Ket d) (A : Matrix d d ℂ) (i j : d) :
    ((MState.pure φ).m * A) i j = φ i * ∑ k, (starRingEnd ℂ) (φ k) * A k j := by
  simp only [Matrix.mul_apply, MState.pure_apply]
  rw [Finset.mul_sum]
  congr 1
  ext k
  ring

/-! ### W2. A vector of squared norm 2: R5 → R6 -/
example {d : Type} [Fintype d] (f : d → ℂ) (hf : ∑ x, ‖f x‖ ^ 2 = 2) :
    ∑ x, (starRingEnd ℂ) (f x) * f x = 2 := by
  simp only [Complex.conj_mul']
  exact_mod_cast hf

/-! ### W3. Constants on both sides of a sum, then a sum that equals 1: R8 → R9 → R10 → R11 → R12, rw, R13 -/
example {d : Type} [Fintype d] (a b : ℂ) (f : d → ℂ) (hf : ∑ k, f k = 1) :
    ∑ k, b * (f k * a) = a * b := by
  calc ∑ k, b * (f k * a) = a * (∑ k, f k) * b := by
        rw [Finset.mul_sum, Finset.sum_mul]
        congr 1
        ext k
        ring
    _ = a * b := by
        rw [hf]
        rw [mul_one]

end M134Guide

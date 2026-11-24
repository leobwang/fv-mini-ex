/- Guide for E109 (Pauli matrices).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other 2×2 complex matrices).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix Complex

namespace E109Guide

/-! # Part R · Reference entries -/

/-! ## From names to literal matrices -/

/-! ### R1. Unfold a definition: `simp only [D]` · goal: the name `D` → its body
`!![a, b; c, d]` is the 2×2 matrix with rows `a b` and `c d`. -/
def D : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 4]
example (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P !![1, 2; 3, 4]) : P D := by
  simp only [D]
  exact h

/-! ### R2. `Matrix.mul_fin_two` · goal: product of two literals → one literal of row-times-column sums
`simp` computes such a product by itself (through `Matrix.cons_mul`, `Matrix.vecMul_cons`, …);
`rw [Matrix.mul_fin_two]` does it in one visible step. -/
example {α : Type} [AddCommMonoid α] [Mul α] (a b c d p q r s : α)
    (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]) :
    P (!![a, b; c, d] * !![p, q; r, s]) := by
  rw [Matrix.mul_fin_two]
  exact h

/-! ### R3. `Matrix.one_fin_two` · goal: the identity matrix `1` → the literal `!![1, 0; 0, 1]`
`simp` never does this by itself: name the lemma (in `rw` or in the `simp` set). -/
example {α : Type} [Zero α] [One α] (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P !![1, 0; 0, 1]) : P 1 := by
  rw [Matrix.one_fin_two]
  exact h

/-! ## Inside the literal: entries, signs, scalars -/

/-! ### R4. `Complex.I_mul_I` · `I * I = -1` · goal: `I * I` → `-1`
`I` is `Complex.I`, the imaginary unit (`open Complex` lets you write `I`). `simp` uses this lemma
by itself. -/
example (P : ℂ → Prop) (h : P (-1)) : P (I * I) := by
  rw [Complex.I_mul_I]
  exact h

/-! ### R5. Negating a literal: `simp` (`Matrix.neg_of`, `Matrix.neg_cons`) · goal: `-!![…]` → entrywise `-` -/
example {α : Type} [Neg α] (a b c d : α) (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P !![-a, -b; -c, -d]) : P (-!![a, b; c, d]) := by
  simp
  exact h

/-! ### R6. Scaling a literal: `simp` (`Matrix.smul_of`, `Matrix.smul_cons`, `smul_eq_mul`) · goal:
`k • !![…]` → every entry multiplied by `k` -/
example {α : Type} [Mul α] (k a b c d : α) (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P !![k * a, k * b; k * c, k * d]) : P (k • !![a, b; c, d]) := by
  simp
  exact h

/-! ### R7. Entry arithmetic: `simp` (`zero_mul`, `one_mul`, `mul_neg`, `mul_one`, `add_zero`, …) · goal -/
example (a b c : ℂ) (P : ℂ → ℂ → Prop) (h : P b (-c)) : P (0 * a + 1 * b) (c * -1 + 0) := by
  simp
  exact h

/-! ### R8. Equation of two literals: `simp` · goal → one equation per entry (closed where they agree) -/
example {α : Type} (a b c d p q r s : α) (h : (a = p ∧ b = q) ∧ c = r ∧ d = s) :
    !![a, b; c, d] = !![p, q; r, s] := by
  simp
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `A = i·[[0,1],[1,0]]`. `simp [A]` stops at `… = -1`: the identity is not a literal (R3) -/
def A : Matrix (Fin 2) (Fin 2) ℂ := !![0, I; I, 0]
example : A * A = -1 := by
  simp [A]
  rw [Matrix.one_fin_two]
  simp

/-! ### W2. The phase gate `S`, one step at a time: R1, R2, then R4, R7, R8 in one `simp` -/
def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, I]
example : S * S = !![1, 0; 0, -1] := by
  simp only [S]
  rw [Matrix.mul_fin_two]
  simp

/-! ### W3. Anticommutation of two other matrices: R1, R2 on both sides, R5, R7, R8 -/
def C : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]
def E : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
example : C * E = -(E * C) := by
  simp only [C, E]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

/-! ### W4. A scalar times a literal: R6, R4, R7, R8 -/
example : I • S = !![I, 0; 0, -1] := by
  simp [S]

end E109Guide

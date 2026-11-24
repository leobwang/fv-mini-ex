/- Guide for M166 (Zero-field transfer matrix).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a diagonal matrix, an upper
triangular matrix, the identity `cosh x + sinh x = exp x`).
Assumed: Lean basics.
-/
import Mathlib

namespace M166Guide

/-! # Part R · Reference entries -/

/-! ## The milestone and the induction -/

/-! ### R1. `have key : M ^ n = C := by …` · context gains `key`; goal unchanged
State the closed form of the whole power as a fact first; the main goal is then one rewrite away. -/
example {α : Type} [Monoid α] (M C : α) (n : ℕ) (P : α → Prop) (hC : M ^ n = C) (h : P C) :
    P (M ^ n) := by
  have key : M ^ n = C := hC
  rw [key]
  exact h

/-! ### R2. `induction n with | zero => … | succ n ih => …` · goal list: one goal per constructor of `ℕ`
With `?_` as each case's proof, both goals stay open and are proved below with `·`.
The `succ` goal gets the induction hypothesis `ih : P n` and must prove `P (n + 1)`. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => ?_
    | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ## Matrix equations → entries -/

/-! ### R3. `ext i j` (lemma `Matrix.ext`) · goal `M = N` → context gains `i j`, goal is one entry -/
example {α : Type} (M N : Matrix (Fin 2) (Fin 2) α) (h : ∀ i j, M i j = N i j) : M = N := by
  ext i j
  exact h i j

/-! ### R4. `fin_cases i` · context loses `i : Fin 2`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`. `exacts [h0, h1]` closes the open goals in
order, one term each. -/
example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  fin_cases i
  exacts [h0, h1]

/-! ## Powers -/

/-! ### R5. `pow_zero` · `a ^ 0 = 1` · goal; for a matrix the `1` is the identity matrix -/
example (M : Matrix (Fin 2) (Fin 2) ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop) (h : P 1) :
    P (M ^ 0) := by
  rw [pow_zero]
  exact h

/-! ### R6. `Matrix.one_apply_eq`, `Matrix.one_apply_ne` · goal: entries of the identity `1` -/
example (P : ℝ → Prop) (h1 : P 1) (h0 : P 0) :
    P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ∧ P ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1) := by
  simp
  exact ⟨h1, h0⟩

/-! ### R7. `add_self_div_two` · `(a + a) / 2 = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P ((a + a) / 2) := by
  rw [add_self_div_two]
  exact h

/-! ### R8. `sub_self`, then `zero_div` · `a - a = 0`, `0 / b = 0` · goal: `(a - a) / b` → `0` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P 0) : P ((a - a) / b) := by
  rw [sub_self]
  rw [zero_div]
  exact h

/-! ### R9. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal; `rw` rewrites only the FIRST power it matches
Here `M ^ (n + 1)` is rewritten, `x ^ (n + 1)` is a different instance and stays. -/
example (M : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) (n : ℕ) (P : Matrix (Fin 2) (Fin 2) ℝ → ℝ → Prop)
    (h : P (M ^ n * M) (x ^ (n + 1))) : P (M ^ (n + 1)) (x ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ## Evaluating one entry (`simp` applies R11 by itself; name R10, R12, R13) -/

/-! ### R10. Unfold a definition: `simp only [D]` · goal: the name `D` → its body -/
noncomputable def D (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x, 0; 0, Real.exp x]
example (x : ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ → Prop) (h : P !![x, 0; 0, Real.exp x]) :
    P (D x) := by
  simp only [D]
  exact h

/-! ### R11. Entry of a literal `!![a, b; c, d] i j` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P c) : P (!![a, b; c, d] 1 0) := by
  simp
  exact h

/-! ### R12. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)
    (P : α → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R13. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ## Hyperbolic functions -/

/-! ### R14. `Real.cosh_eq` · `cosh x = (exp x + exp (-x)) / 2` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((Real.exp x + Real.exp (-x)) / 2)) : P (Real.cosh x) := by
  rw [Real.cosh_eq]
  exact h

/-! ### R15. `Real.sinh_eq` · `sinh x = (exp x - exp (-x)) / 2` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((Real.exp x - Real.exp (-x)) / 2)) : P (Real.sinh x) := by
  rw [Real.sinh_eq]
  exact h

/-! ### R16. `ring` · closes a commutative-ring identity; `Real.exp x`, `Real.exp (-x)` are unknowns
It does not know `exp x * exp (-x) = 1`; the identities here never need it. -/
example (u v a b : ℝ) :
    (a + b) / 2 * u + (a - b) / 2 * v = (a * (u + v) + b * (u - v)) / 2 := by ring

/-! ## The trace -/

/-! ### R17. `Matrix.trace_fin_two` · `A.trace = A 0 0 + A 1 1` · goal -/
example {α : Type} [AddCommMonoid α] (A : Matrix (Fin 2) (Fin 2) α) (P : α → Prop)
    (h : P (A 0 0 + A 1 1)) : P A.trace := by
  rw [Matrix.trace_fin_two]
  exact h

/-! ### R18. `add_halves` · `a / 2 + a / 2 = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a / 2 + a / 2) := by
  rw [add_halves]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A closed form for a power, by induction: R2, R9, `rw [ih]`, R3, R4, then `simp` -/
example (a b : ℝ) (n : ℕ) : !![a, 0; 0, b] ^ n = !![a ^ n, 0; 0, b ^ n] := by
  induction n with
    | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-! ### W2. Same pattern; `simp` leaves one entry, `1 + ↑n = ↑n + 1`, and `ring` (R16) closes it
When `simp` leaves an arithmetic goal in EVERY entry, write `simp [...] <;> ring` instead. -/
example (n : ℕ) : !![(1 : ℝ), 1; 0, 1] ^ n = !![1, (n : ℝ); 0, 1] := by
  induction n with
    | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring

/-! ### W3. Trace of a literal: R17, then `simp` evaluates the two entries -/
example (a b c d : ℝ) : Matrix.trace !![a, b; c, d] = a + d := by
  rw [Matrix.trace_fin_two]
  simp

/-! ### W4. cosh and sinh in terms of exp: R14, R15, then R16 -/
example (x : ℝ) : Real.cosh x + Real.sinh x = Real.exp x := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

end M166Guide

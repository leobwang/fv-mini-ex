/- Guide for E104 (Polynomial evaluation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on polynomials that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Polynomial

namespace E104Guide

/-! # Part R · Reference entries -/

/-! ## `eval` distributes over the operations (`simp` and `norm_num` apply these by themselves)
`p.eval x` is printed `eval x p`: the point comes first. `R[X]` is the type of polynomials with
coefficients in `R`; `[CommRing R]` says `R` has `+`, `-`, `*` with the usual laws (`ℝ`, `ℚ`, `ℤ` do). -/

/-! ### R1. `eval_add` · `eval x (p + q) = eval x p + eval x q` · goal -/
example {R : Type} [CommRing R] (p q : R[X]) (x : R) (P : R → Prop)
    (h : P (eval x p + eval x q)) : P (eval x (p + q)) := by
  rw [eval_add]
  exact h

/-! ### R2. `eval_sub` · `eval x (p - q) = eval x p - eval x q` · goal -/
example {R : Type} [CommRing R] (p q : R[X]) (x : R) (P : R → Prop)
    (h : P (eval x p - eval x q)) : P (eval x (p - q)) := by
  rw [eval_sub]
  exact h

/-! ### R3. `eval_mul` · `eval x (p * q) = eval x p * eval x q` · goal -/
example {R : Type} [CommRing R] (p q : R[X]) (x : R) (P : R → Prop)
    (h : P (eval x p * eval x q)) : P (eval x (p * q)) := by
  rw [eval_mul]
  exact h

/-! ### R4. `eval_pow` · `eval x (p ^ n) = eval x p ^ n` · goal -/
example {R : Type} [CommRing R] (p : R[X]) (n : ℕ) (x : R) (P : R → Prop)
    (h : P (eval x p ^ n)) : P (eval x (p ^ n)) := by
  rw [eval_pow]
  exact h

/-! ### R5. `eval_X` · `eval x X = x` · goal: the variable `X` becomes the point
`rw` replaces every `eval x X` in the goal at once. -/
example {R : Type} [CommRing R] (x : R) (P : R → Prop) (h : P x) : P (eval x X) := by
  rw [eval_X]
  exact h

/-! ### R6. `eval_C` · `eval x (C a) = a` · goal: a constant polynomial evaluates to its constant -/
example {R : Type} [CommRing R] (a x : R) (P : R → Prop) (h : P a) : P (eval x (C a)) := by
  rw [eval_C]
  exact h

/-! ### R7. `eval_ofNat`, `eval_one` · goal: a numeral polynomial evaluates to the same numeral
In `2 * X : R[X]` the `2` is a polynomial (the constant `2`), so `eval` must clear it too:
`eval x 2 = 2` (numerals `≥ 2`, `eval_ofNat`) and `eval x 1 = 1` (`eval_one`). -/
example {R : Type} [CommRing R] (x : R) (P : R → R → Prop) (h : P 2 1) :
    P (eval x (2 : R[X])) (eval x (1 : R[X])) := by
  rw [eval_ofNat, eval_one]
  exact h

/-! ## Closing the arithmetic -/

/-! ### R8. `norm_num` · closes a goal made of numerals; it also runs R1–R7 by itself -/
example : (5 : ℝ) ^ 2 - 3 * 5 + 2 = 12 := by
  norm_num

/-! ## Roots -/

/-! ### R9. `IsRoot.eq_zero` · `p.IsRoot r → eval r p = 0` · context gains the equation
`p.IsRoot r` is defined as `eval r p = 0`, but `rw` and `simp` only see the name `IsRoot`. -/
example {R : Type} [CommRing R] (p : R[X]) (r : R) (h : p.IsRoot r) : eval r p = 0 := by
  have h0 := h.eq_zero
  exact h0

/-! ### R10. `zero_mul` · `0 * a = 0` · goal -/
example {R : Type} [CommRing R] (a : R) (P : R → Prop) (h : P 0) : P (0 * a) := by
  rw [zero_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's polynomials) -/

/-! ### W1. A concrete polynomial, one lemma at a time: R1, R3, R4, R5, R6, then R8 -/
example : (X ^ 3 + C 2 * X : ℝ[X]).eval 2 = 12 := by
  rw [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  norm_num

/-! ### W2. The same in one call: `norm_num` (R8) applies R1–R7 itself -/
example : (X ^ 3 + C 2 * X : ℝ[X]).eval 2 = 12 := by
  norm_num

/-! ### W3. Unknown polynomials with known values: R2, R3, R6, then `rw [hp, hq]`, then R8 -/
example (p q : ℝ[X]) (x : ℝ) (hp : p.eval x = 3) (hq : q.eval x = 4) :
    (p - q * C 2).eval x = -5 := by
  rw [eval_sub, eval_mul, eval_C]
  rw [hp, hq]
  norm_num

/-! ### W4. A root of `p` makes `X ^ 2 * p` vanish: plain `simp` only splits the product
(`a * b = 0 ↔ a = 0 ∨ b = 0`); rewriting with the equation from R9 instead finishes it. -/
example (p : ℝ[X]) (r : ℝ) (h : p.IsRoot r) : (X ^ 2 * p).eval r = 0 := by
  simp
  right
  exact h.eq_zero

example (p : ℝ[X]) (r : ℝ) (h : p.IsRoot r) : (X ^ 2 * p).eval r = 0 := by
  rw [eval_mul]
  rw [h.eq_zero]
  rw [mul_zero]

end E104Guide

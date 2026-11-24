/- Guide for M187 (Derivative of physicists' Hermite polynomials).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the family `Xpow n = Xⁿ`, a
general polynomial `f`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Mathematics.SpecialFunctions.PhysHermite

open Polynomial

namespace M187Guide

/-! # Part R · Reference entries -/

/-! ## Induction on `n : ℕ` -/

/-! ### R1. `induction n with | zero => … | succ n ih => …` · goal list: `zero` and `succ`; context: `ih`
Without `with` (shown here) the `succ` variable and hypothesis are inaccessible (`n✝`, `a✝`); with
`with`, indent the `|` alternatives under `induction` and they are named `n` and `ih`. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n
  exact h0
  exact hs _ ‹_›

/-! ## The Hermite polynomials (physlib) -/

/-! ### R2. `physHermite_one` · `physHermite 1 = 2 * X` · goal
A `@[simp]` lemma: plain `simp` uses it too; `simp [physHermite_one]` just makes that explicit.
`ℤ[X]` is `Polynomial ℤ`; `X` is the variable; `2 : ℤ[X]` is the constant polynomial 2. -/
example (P : ℤ[X] → Prop) (h : P (2 * X)) : P (physHermite 1) := by
  rw [physHermite_one]
  exact h

/-! ### R3. `physHermite_zero` · `physHermite 0 = C 1`, then `C_1` · `C 1 = 1` · goal
`C a` is the constant polynomial `a`; `C_1` turns `C 1` into the polynomial `1`. `simp` applies both. -/
example (P : ℤ[X] → Prop) (h : P 1) : P (physHermite 0) := by
  rw [physHermite_zero]
  rw [C_1]
  exact h

/-! ### R4. `physHermite_succ` · `physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n)` · goal
Give the argument: `rw [physHermite_succ m]` rewrites exactly `physHermite (m + 1)`, every copy of it. -/
example (m : ℕ) (P : ℤ[X] → Prop) (h : P (2 • X * physHermite m - derivative (physHermite m))) :
    P (physHermite (m + 1)) := by
  rw [physHermite_succ m]
  exact h

/-! ## Differentiating (`derivative : R[X] → R[X]` is the formal derivative) -/

/-! ### R5. `derivative_mul` · `derivative (f * g) = derivative f * g + f * derivative g` · goal -/
example {R : Type} [Semiring R] (f g : R[X]) (P : R[X] → Prop)
    (h : P (derivative f * g + f * derivative g)) : P (derivative (f * g)) := by
  rw [derivative_mul]
  exact h

/-! ### R6. `derivative_sub` · `derivative (f - g) = derivative f - derivative g` · goal
Needs subtraction: `[Ring R]` (ℤ qualifies, ℕ does not). -/
example {R : Type} [Ring R] (f g : R[X]) (P : R[X] → Prop)
    (h : P (derivative f - derivative g)) : P (derivative (f - g)) := by
  rw [derivative_sub]
  exact h

/-! ### R7. `derivative_X` · `derivative X = 1` · goal -/
example {R : Type} [Semiring R] (P : R[X] → Prop) (h : P 1) : P (derivative (X : R[X])) := by
  rw [derivative_X]
  exact h

/-! ### R8. `derivative_ofNat` · `derivative (OfNat.ofNat n) = 0` for a numeral `n ≥ 2` · goal -/
example {R : Type} [Semiring R] (P : R[X] → Prop) (h : P 0) : P (derivative (2 : R[X])) := by
  rw [derivative_ofNat]
  exact h

/-! ### R9. `derivative_natCast`, `derivative_one` · `derivative ↑n = 0`, `derivative 1 = 0` · goal
`↑n` is the natural number `n` cast to the constant polynomial `n`. -/
example {R : Type} [Semiring R] (n : ℕ) (P : R[X] → Prop) (h : P 0) :
    P (derivative (n : R[X])) := by
  rw [derivative_natCast]
  exact h

example {R : Type} [Semiring R] (P : R[X] → Prop) (h : P 0) : P (derivative (1 : R[X])) := by
  rw [derivative_one]
  exact h

/-! ### R10. `derivative_add` · `derivative (f + g) = derivative f + derivative g` · goal -/
example {R : Type} [Semiring R] (f g : R[X]) (P : R[X] → Prop)
    (h : P (derivative f + derivative g)) : P (derivative (f + g)) := by
  rw [derivative_add]
  exact h

/-! ## Natural-number scalars and casts -/

/-! ### R11. `nsmul_eq_mul` · `k • a = ↑k * a` for `k : ℕ` · goal
`k • a` with `k : ℕ` is `a + ⋯ + a` (k times); the lemma turns it into a product with the cast `↑k`. -/
example {α : Type} [NonAssocSemiring α] (k : ℕ) (a : α) (P : α → Prop) (h : P (↑k * a)) :
    P (k • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R12. `Nat.cast_ofNat` · `↑(OfNat.ofNat n) = OfNat.ofNat n` · goal: `↑2` → `2`
After R11 on `2 • X` the goal shows `↑2 * X` (the natural number 2, cast); this removes the cast. -/
example {R : Type} [Semiring R] (P : R[X] → Prop) (h : P (2 * X)) : P (((2 : ℕ) : R[X]) * X) := by
  rw [Nat.cast_ofNat]
  exact h

/-! ### R13. `Nat.cast_add`, `Nat.cast_one` · `↑(m + k) = ↑m + ↑k`, `↑1 = 1` · goal
`push_cast` and `simp` apply both. -/
example {R : Type} [Semiring R] (n : ℕ) (P : R[X] → Prop) (h : P (↑n + 1)) :
    P (((n + 1 : ℕ) : R[X])) := by
  rw [Nat.cast_add, Nat.cast_one]
  exact h

/-! ## Closing -/

/-! ### R14. `ring` · closes a commutative-ring identity in `ℤ[X]`
It treats `X`, `↑n`, `p` and `derivative p` as unknowns: it knows neither the Hermite recursion nor
how `derivative` acts. -/
example (n : ℕ) (p q : ℤ[X]) :
    2 * (X * p - q) + 2 * (((n : ℤ[X]) + 1) * q) = 2 * X * p + 2 * (n : ℤ[X]) * q := by ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `rw [ih]` rewrites every copy, also the one inside `derivative (derivative f)` -/
example (f q : ℤ[X]) (ih : derivative f = q) (P : ℤ[X] → Prop) (h : P (X * q - derivative q)) :
    P (X * derivative f - derivative (derivative f)) := by
  rw [ih]
  exact h

/-! ### W2. What `simp` does to the derivatives R5 leaves: R7–R13 plus `0 * p = 0`, `p * 1 = p` -/
example (n : ℕ) (q : ℤ[X]) :
    derivative (2 • X) * q - derivative ((n + 1) • q) = 2 * q - ((n : ℤ[X]) + 1) * derivative q := by
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, derivative_mul,
    derivative_ofNat, derivative_X, derivative_add, derivative_natCast, derivative_one,
    zero_mul, mul_one, zero_add, add_zero]

/-! ### W3. The same induction pattern on another family: `Xpow n = Xⁿ`, `(Xⁿ⁺¹)' = (n + 1) • Xⁿ` -/
noncomputable def Xpow : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * Xpow n

theorem Xpow_succ (n : ℕ) : Xpow (n + 1) = X * Xpow n := rfl

example (n : ℕ) : derivative (Xpow (n + 1)) = (n + 1) • Xpow n := by
  induction n with
    | zero => simp [Xpow]
    | succ n ih =>
      rw [Xpow_succ (n + 1), derivative_mul, ih, Xpow_succ n]
      simp
      ring

end M187Guide

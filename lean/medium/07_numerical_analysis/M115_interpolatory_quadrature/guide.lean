/- Guide for M115 (Interpolatory quadrature is exact).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other polynomials and sums).
Assumed: Lean basics.
-/
import Mathlib

open Polynomial

namespace M115Guide

/-! # Part R · Reference entries -/

/-! ## Rewriting one side only -/

/-! ### R1. `conv_lhs => rw [h]` · goal: rewrite inside the left-hand side of `=` only
`rw [h]` would rewrite every `a`, on both sides. `conv_rhs` is the mirror image. -/
example {α β : Type} (F G : α → β) (a b : α) (h : a = b) (h' : F b = G a) : F a = G a := by
  conv_lhs => rw [h]
  exact h'

/-! ## Lagrange interpolation -/

/-! ### R2. `Lagrange.eq_interpolate` · goal: a polynomial → the interpolant of its own values
`Set.InjOn v ↑s → q.degree < ↑s.card → q = Lagrange.interpolate s v (fun i => eval (v i) q)`. -/
example {F ι : Type} [Field F] [DecidableEq ι] (s : Finset ι) (v : ι → F) (hv : Set.InjOn v s)
    (q : F[X]) (hq : q.degree < s.card) (P : F[X] → Prop)
    (h : P (Lagrange.interpolate s v fun i => eval (v i) q)) : P q := by
  rw [Lagrange.eq_interpolate hv hq]
  exact h

/-! ### R3. `Lagrange.interpolate_apply` · goal: the interpolant → its sum over the basis
`Lagrange.interpolate s v r = ∑ i ∈ s, C (r i) * Lagrange.basis s v i`. -/
example {F ι : Type} [Field F] [DecidableEq ι] (s : Finset ι) (v r : ι → F) (P : F[X] → Prop)
    (h : P (∑ i ∈ s, C (r i) * Lagrange.basis s v i)) : P (Lagrange.interpolate s v r) := by
  rw [Lagrange.interpolate_apply]
  exact h

/-! ## Evaluating polynomials (use `simp only`: they sit under the integral's `fun x`) -/

/-! ### R4. `Polynomial.eval_finsetSum` · goal: `eval` of a sum → sum of `eval`s -/
example {R ι : Type} [Semiring R] (s : Finset ι) (g : ι → R[X]) (x : R) (P : R → Prop)
    (h : P (∑ i ∈ s, eval x (g i))) : P (eval x (∑ i ∈ s, g i)) := by
  simp only [eval_finsetSum]
  exact h

/-! ### R5. `Polynomial.eval_mul` · goal: `eval` of a product → product of `eval`s -/
example {R : Type} [CommSemiring R] (q r : R[X]) (x : R) (P : R → Prop)
    (h : P (eval x q * eval x r)) : P (eval x (q * r)) := by
  simp only [eval_mul]
  exact h

/-! ### R6. `Polynomial.eval_C` · goal: `eval` of a constant polynomial → the constant -/
example {R : Type} [Semiring R] (c x : R) (P : R → Prop) (h : P c) : P (eval x (C c)) := by
  simp only [eval_C]
  exact h

/-! ## Integrals of finite sums -/

/-! ### R7. `intervalIntegral.integral_finsetSum` · goal: `∫ ∑` → `∑ ∫`, plus side goal (integrability)
`(∀ i ∈ s, IntervalIntegrable (f i) μ a b) → ∫ x in a..b, ∑ i ∈ s, f i x ∂μ = ∑ i ∈ s, ∫ x in a..b, f i x ∂μ`. -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ) (P : ℝ → Prop)
    (h : P (∑ i ∈ s, ∫ x in a..b, f i x))
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    P (∫ x in a..b, ∑ i ∈ s, f i x) := by
  rw [intervalIntegral.integral_finsetSum]
  exact h
  exact hf

/-! ### R8. `IntervalIntegrable.const_mul` · goal: integrability of `c * f x` → integrability of `f` -/
example (f : ℝ → ℝ) (c a b : ℝ) (h : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => c * f x) MeasureTheory.volume a b := by
  apply IntervalIntegrable.const_mul
  exact h

/-! ### R9. `Continuous.intervalIntegrable` · goal: integrability on `[a, b]` → continuity -/
example (f : ℝ → ℝ) (a b : ℝ) (h : Continuous f) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact h

/-! ### R10. `Polynomial.continuous` · closes `Continuous fun x => eval x q` -/
example (q : ℝ[X]) : Continuous fun x => eval x q := by
  exact Polynomial.continuous q

/-! ## Comparing two sums term by term -/

/-! ### R11. `Finset.sum_congr rfl` · goal: `∑ f = ∑ g` → context gains `i, hi : i ∈ s`, goal `f i = g i` -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, f i = g i) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  exact h i hi

/-! ### R12. `intervalIntegral.integral_const_mul` · goal: a constant factor moves out of `∫` -/
example (f : ℝ → ℝ) (c a b : ℝ) (P : ℝ → Prop) (h : P (c * ∫ x in a..b, f x)) :
    P (∫ x in a..b, c * f x) := by
  rw [intervalIntegral.integral_const_mul]
  exact h

/-! ### R13. `mul_comm` · goal: `a * b` → `b * a` (the first product `rw` finds) -/
example {α : Type} [CommMonoid α] (a b : α) (P : α → Prop) (h : P (b * a)) : P (a * b) := by
  rw [mul_comm]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A constant times a polynomial, integrated: R5, R6, then R12 -/
example (q : ℝ[X]) (c a b : ℝ) : ∫ x in a..b, eval x (C c * q) = c * ∫ x in a..b, eval x q := by
  simp only [eval_mul, eval_C]
  rw [intervalIntegral.integral_const_mul]

/-! ### W2. The integral of a sum of polynomials: R4, R7, then R9 → R10 on the side goal -/
example {ι : Type} (s : Finset ι) (g : ι → ℝ[X]) (a b : ℝ) :
    ∫ x in a..b, eval x (∑ i ∈ s, g i) = ∑ i ∈ s, ∫ x in a..b, eval x (g i) := by
  simp only [eval_finsetSum]
  rw [intervalIntegral.integral_finsetSum]
  intro i _
  exact (Polynomial.continuous (g i)).intervalIntegrable a b

/-! ### W3. Interpolating on the right only: `conv_rhs` with R2, R3 -/
example {ι : Type} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ) (hv : Set.InjOn v s) (q : ℝ[X])
    (hq : q.degree < s.card) (x : ℝ) :
    eval x (∑ i ∈ s, C (eval (v i) q) * Lagrange.basis s v i) = eval x q := by
  conv_rhs => rw [Lagrange.eq_interpolate hv hq]
  conv_rhs => rw [Lagrange.interpolate_apply]

/-! ### W4. The side goal of R7 in one term: R10, R9, R8 composed with dot notation -/
example (q : ℝ[X]) (c a b : ℝ) :
    IntervalIntegrable (fun x => c * eval x q) MeasureTheory.volume a b :=
  ((Polynomial.continuous q).intervalIntegrable a b).const_mul c

end M115Guide

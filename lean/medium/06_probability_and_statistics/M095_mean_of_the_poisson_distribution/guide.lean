/- Guide for M095 (Mean of the Poisson distribution).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other series, other summands).
Assumed: Lean basics.
-/
import Mathlib

open ProbabilityTheory MeasureTheory
open scoped NNReal

namespace M095Guide

/-! # Part R · Reference entries -/

/-! ## From the expectation to a series -/

/-! ### R1. `integral_poissonMeasure` · goal: an integral against `Po(r)` → a series `∑'`
`∫ n, g n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / n!) • g n`: the expectation of `g` is the
probability-weighted sum of its values. -/
example (r : ℝ≥0) (g : ℕ → ℝ) (P : ℝ → Prop)
    (h : P (∑' n, (Real.exp (-r) * r ^ n / n.factorial) • g n)) :
    P (∫ n, g n ∂(poissonMeasure r)) := by
  rw [integral_poissonMeasure]
  exact h

/-! ### R2. `set f : ℕ → ℝ := e with hf` · context gains `f := e` and `hf : f = e`; goal: `e` → `f`
Every copy of the expression `e` in the goal is replaced by the new name `f`. -/
example (c : ℝ) (P : (ℕ → ℝ) → Prop) (h : ∀ f : ℕ → ℝ, P f) : P (fun n => c * n) := by
  set f : ℕ → ℝ := fun n => c * n with hf
  exact h f

/-! ### R3. `HasSum.tsum_eq` · closes `∑' n, f n = a` from `HasSum f a`
`HasSum f a`: the series `∑ f n` converges (unconditionally) to `a`. `∑' n, f n` (also printed
`tsum f`) is its value, defined as `0` when the series does not converge. -/
example (f : ℕ → ℝ) (a : ℝ) (h : HasSum f a) : ∑' n, f n = a := by
  exact h.tsum_eq

/-! ## Building a `HasSum` from the total probability -/

/-! ### R4. `hasSum_one_poissonMeasure r` · context gains: the Poisson probabilities sum to `1` -/
example (r : ℝ≥0) (G : Prop)
    (g : HasSum (fun n => Real.exp (-r) * r ^ n / n.factorial) 1 → G) : G := by
  have h1 := hasSum_one_poissonMeasure r
  exact g h1

/-! ### R5. `HasSum.mul_left c` · context gains: multiply a convergent series by a constant `c` -/
example (f : ℕ → ℝ) (a c : ℝ) (h : HasSum f a) (G : Prop)
    (g : HasSum (fun i => c * f i) (c * a) → G) : G := by
  have h2 := h.mul_left c
  exact g h2

/-! ### R6. `rw [mul_one] at h` · context: the hypothesis `h` is rewritten, the goal is unchanged
`mul_one : a * 1 = a`. `rw [lemma] at h` rewrites inside `h` instead of the goal. -/
example {α : Type} [MulOneClass α] (a : α) (P : α → Prop) (h : P (a * 1)) : P a := by
  rw [mul_one] at h
  exact h

/-! ## A function identity, pointwise -/

/-! ### R7. `funext n` · goal: an equation of functions → the equation at an arbitrary `n` -/
example {α β : Type} (f g : α → β) (h : ∀ x, f x = g x) : f = g := by
  funext n
  exact h n

/-! ### R8. `simp only [hf]` with `hf : f = fun n => …` · goal: `f t` → the body with `n := t` -/
example (c : ℝ) (f : ℕ → ℝ) (hf : f = fun n : ℕ => c * n) (k : ℕ) (P : ℝ → Prop)
    (h : P (c * ↑(k + 1))) : P (f (k + 1)) := by
  simp only [hf]
  exact h

/-! ### R9. `smul_eq_mul` · goal: `a • b` → `a * b` (scalar action of a ring on itself is `*`) -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R10. `Nat.factorial_succ` · goal: `(n + 1)! → (n + 1) * n!` -/
example (n : ℕ) (P : ℕ → Prop) (h : P ((n + 1) * n.factorial)) : P (n + 1).factorial := by
  rw [Nat.factorial_succ]
  exact h

/-! ### R11. `push_cast` · goal: casts `↑` moved inward, past `*`, `+`, numerals -/
example (m n : ℕ) (P : ℝ → Prop) (h : P ((↑m + 1) * ↑n)) : P (↑((m + 1) * n)) := by
  push_cast
  exact h

/-! ### R12. `field_simp` · goal: denominators cleared (needs to know they are `≠ 0`)
It proves `↑n.factorial ≠ 0` and `↑n + 1 ≠ 0` by itself; other denominators need a hypothesis
`hb : b ≠ 0` in the context. -/
example (a c : ℝ) (n : ℕ) (h : a = ↑n.factorial * c) : a / ↑n.factorial = c := by
  field_simp
  exact h

/-! ### R13. `ring` · closes a commutative-ring identity; `x ^ (n + 1) = x * x ^ n` included -/
example (x : ℝ) (n : ℕ) : x ^ (n + 1) = x * x ^ n := by
  ring

/-! ## Shifting the index -/

/-! ### R14. `hasSum_nat_add_iff' k` · goal: `HasSum f g` → the series from index `k` on
`HasSum (fun n => f (n + k)) (g - ∑ i ∈ Finset.range k, f i) ↔ HasSum f g`; use it right to left. -/
example (f : ℕ → ℝ) (g : ℝ)
    (h : HasSum (fun n => f (n + 1)) (g - ∑ i ∈ Finset.range 1, f i)) : HasSum f g := by
  rw [← hasSum_nat_add_iff' 1]
  exact h

/-! ### R15. `Finset.sum_range_one` · goal: `∑ i ∈ Finset.range 1, f i` → `f 0` (`simp` uses it) -/
example (f : ℕ → ℝ) (P : ℝ → Prop) (h : P (f 0)) : P (∑ i ∈ Finset.range 1, f i) := by
  rw [Finset.sum_range_one]
  exact h

/-! ### R16. `simpa [l] using h` · closes the goal: simplifies goal and `h` with `l`, then matches -/
example (f : ℕ → ℝ) (a : ℝ) (h0 : f 0 = 0) (h : HasSum f a) :
    HasSum f (a - ∑ i ∈ Finset.range 1, f i) := by
  simpa [h0] using h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Scaling a known sum, then reading off `∑'`: R5, R6, R3 -/
example (g : ℕ → ℝ) (h : HasSum g 1) : ∑' n, 3 * g n = 3 := by
  have h3 := h.mul_left 3
  rw [mul_one] at h3
  exact h3.tsum_eq

/-! ### W2. Unshifting a series whose term `0` vanishes: R14, R15, R16 -/
example (g : ℕ → ℝ) (a : ℝ) (h0 : g 0 = 0) (h : HasSum (fun n => g (n + 1)) a) : HasSum g a := by
  rw [← hasSum_nat_add_iff' 1]
  simpa [h0] using h

/-! ### W3. A factorial identity, pointwise: R7, R10, R11, R12, R13 (two factors this time) -/
example (x : ℝ) :
    (fun n : ℕ => x ^ (n + 2) / (n + 2).factorial * ((n + 2 : ℕ) * (n + 1 : ℕ))) =
      fun n => x ^ 2 * (x ^ n / n.factorial) := by
  funext n
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end M095Guide

/- Guide for M051 (Gauss sum).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use `induction n with | zero => ?_ | succ k ih => ?_` so that both cases show up as
goals in the infoview; in the exercise you may put the tactics right after each `=>` instead.
Part W: worked combinations on other sums (cubes, `3i² + 3i + 1`), not on the exercise's.
Assumed: Lean basics (easy tier E001–E033), in particular `induction` on `Nat` (E014).
-/
import Mathlib

open Finset

namespace M051Guide

/-! # Part R · Reference entries -/

/-! ## Splitting `n` into `0` and `k + 1` -/

/-! ### R1. `induction n with | zero => ?_ | succ k ih => ?_` · goal list: one goal → two goals
Case `zero`: `n` is replaced by `0`. Case `succ`: `n` is replaced by `k + 1`, and the context gains
`k` and the induction hypothesis `ih : P k`. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ k ih => ?_
  · exact h0
  · exact hs k ih

/-! ## The `zero` case: empty and one-term sums -/

/-! ### R2. `Finset.sum_range_zero` · `∑ i ∈ range 0, f i = 0` · goal: the empty sum → `0` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (P : M → Prop) (h : P 0) :
    P (∑ i ∈ range 0, f i) := by
  rw [Finset.sum_range_zero]
  exact h

/-! ### R3. `Finset.sum_range_one` · `∑ i ∈ range 1, f i = f 0` · goal: a one-term sum → its term -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (P : M → Prop) (h : P (f 0)) :
    P (∑ i ∈ range 1, f i) := by
  rw [Finset.sum_range_one]
  exact h

/-! ### R4. `simp` · closes a `zero` case: it does what R2/R3 do by hand (via its own lemmas
`Finset.range_zero`, `Finset.sum_empty`, `Finset.range_one`, `Finset.sum_singleton`) and the numeral
facts `0 + 1 = 1`, `0 * a = 0`, `0 ^ 2 = 0`, so a base case made of an empty or one-term sum and
numerals goes away in one step. -/
example (f : ℕ → ℕ) : 3 * ∑ i ∈ range (0 + 1), f i = 3 * f 0 := by
  simp

/-! ## The `succ` case: peel off the last term -/

/-! ### R5. `Finset.sum_range_succ` · `∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`
· goal: a sum up to `n + 1` → the sum up to `n` plus the last term `f n` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∑ x ∈ range n, f x + f n)) : P (∑ x ∈ range (n + 1), f x) := by
  rw [Finset.sum_range_succ]
  exact h

/-! ### R6. `mul_add` · `a * (b + c) = a * b + a * c` · goal: distribute a factor over `+` -/
example {α : Type} [Semiring α] (a b c : α) (P : α → Prop) (h : P (a * b + a * c)) :
    P (a * (b + c)) := by
  rw [mul_add]
  exact h

/-! ### R7. `rw [ih]` · goal: the left side of the induction hypothesis → its right side
`rw` needs `ih`'s left side `c * s` to appear literally. In `c * (s + u)` it does not; R6 makes it
appear. -/
example (c s t u : ℕ) (ih : c * s = t) (P : ℕ → Prop) (h : P (t + c * u)) :
    P (c * s + c * u) := by
  rw [ih]
  exact h

/-! ## Arithmetic left over -/

/-! ### R8. `ring` · closes an identity of commutative (semi)rings, `ℕ` included: `+`, `*`, `^` by
numerals, numerals; unknowns such as `a`, `b` stay symbols. It does not use hypotheses. -/
example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Sum of cubes, `4 · (0³ + 1³ + … + n³) = (n (n + 1))²`: R1; R4 for `zero`; R5, R6, R7,
R8 for `succ`. -/
example (n : ℕ) : 4 * ∑ i ∈ range (n + 1), i ^ 3 = (n * (n + 1)) ^ 2 := by
  induction n with | zero => ?_ | succ k ih => ?_
  · simp
  rw [Finset.sum_range_succ]
  rw [mul_add]
  rw [ih]
  ring

/-! ### W2. `∑_{i<n} (3i² + 3i + 1) = n³`: no factor in front of the sum, so no R6. -/
example (n : ℕ) : ∑ i ∈ range n, (3 * i ^ 2 + 3 * i + 1) = n ^ 3 := by
  induction n with | zero => ?_ | succ k ih => ?_
  · simp
  rw [Finset.sum_range_succ]
  rw [ih]
  ring

end M051Guide

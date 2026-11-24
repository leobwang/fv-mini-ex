/- Guide for E042 (Finset sums).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on sums that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `rw`, `simp [...]`, `decide`, `exact`.
Mathlib's `Finset ι` is a finite set of elements of `ι`; `Finset.range n = {0, 1, …, n - 1}`; and
`∑ i ∈ s, f i` (typed `\sum`, `\in`) is `Finset.sum s f`, the sum of `f i` over all `i ∈ s`.
-/
import Mathlib

open Finset

namespace E042Guide

/-! # Part R · Reference entries -/

/-! ## Peeling terms off a sum over `range` -/

/-! ### R1. `Finset.sum_range_succ` · goal: `∑ over range (n + 1)` → `∑ over range n` plus the last term
`sum_range_succ f n : ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`. -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∑ x ∈ range n, f x + f n)) : P (∑ i ∈ range (n + 1), f i) := by
  rw [Finset.sum_range_succ]
  exact h

/-! ### R2. `Finset.sum_range_succ` on `range (n + 2)` or `range 3` · goal: same peel
`rw` matches `n + 2` with `?m + 1` (taking `?m := n + 1`) and the numeral `3` with `?m + 1` (taking
`?m := 2`), so no rewrite of `n + 2` into `n + 1 + 1` is needed first. -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∑ x ∈ range (n + 1), f x + f (n + 1))) : P (∑ i ∈ range (n + 2), f i) := by
  rw [Finset.sum_range_succ]
  exact h

example {M : Type} [AddCommMonoid M] (f : ℕ → M) (P : M → Prop)
    (h : P (∑ x ∈ range 2, f x + f 2)) : P (∑ i ∈ range 3, f i) := by
  rw [Finset.sum_range_succ]
  exact h

/-! ### R3. `Finset.sum_range_zero` · goal: the empty sum `∑ over range 0` → `0` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (P : M → Prop) (h : P 0) :
    P (∑ k ∈ range 0, f k) := by
  rw [Finset.sum_range_zero]
  exact h

/-! ### R4. `simp [Finset.sum_range_succ]` · goal: a sum over `range 3` unrolled to `f 0 + f 1 + f 2`
`simp` applies R2 until it reaches `range 0`, then R3 (a `simp` lemma already) and `0 + a = a`.
On numerals it also does the arithmetic, so a goal such as `∑ i ∈ range 3, i = 3` closes. -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (P : M → Prop) (h : P (f 0 + f 1 + f 2)) :
    P (∑ i ∈ range 3, f i) := by
  simp [Finset.sum_range_succ]
  exact h

/-! ## Linearity of a sum -/

/-! ### R5. `Finset.sum_add_distrib` · goal: the sum of a `+` → a `+` of two sums
`sum_add_distrib : ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x`. -/
example {ι M : Type} [AddCommMonoid M] (s : Finset ι) (f g : ι → M) (P : M → Prop)
    (h : P (∑ x ∈ s, f x + ∑ x ∈ s, g x)) : P (∑ i ∈ s, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R6. `Finset.mul_sum` · goal: a constant times a sum → the sum of constant-times-terms
`mul_sum s f a : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `rw [← Finset.mul_sum]` goes back. -/
example {ι R : Type} [Semiring R] (s : Finset ι) (f : ι → R) (a : R) (P : R → Prop)
    (h : P (∑ i ∈ s, a * f i)) : P (a * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact h

example {ι R : Type} [Semiring R] (s : Finset ι) (f : ι → R) (a : R) (P : R → Prop)
    (h : P (a * ∑ i ∈ s, f i)) : P (∑ i ∈ s, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! # Part W · Worked combinations (not the exercise's sums) -/

/-! ### W1. R4 on numerals: the first four odd numbers add up to `4 ^ 2` -/
example : ∑ i ∈ range 4, (2 * i + 1) = 16 := by
  simp [Finset.sum_range_succ]

/-! ### W2. R1/R2 three times: peel three terms off a sum over `range (m + 3)`
The last `rw` leaves both sides identical, and `rw` closes such a goal with `rfl` by itself. -/
example (g : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ range (m + 3), g i = ∑ i ∈ range m, g i + g m + g (m + 1) + g (m + 2) := by
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]

/-! ### W3. R5 twice, then R6: a sum of three terms, one with a constant factor
`+` groups to the left, so `f i + g i + 5 * k i` is `(f i + g i) + 5 * k i`: the first R5 splits
off `5 * k i`, the second splits `f i + g i`. -/
example (s : Finset ℕ) (f g k : ℕ → ℤ) :
    ∑ i ∈ s, (f i + g i + 5 * k i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i + 5 * ∑ i ∈ s, k i := by
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.mul_sum]

end E042Guide

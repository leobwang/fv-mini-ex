/- Guide for E070 (Products and Fin sums).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other products and sums).
Assumed: Lean basics (E001–E033) and E042 (sums `∑ i ∈ range n, f i`).
-/
import Mathlib

open Finset

namespace E070Guide

/-! # Part R · Reference entries -/

/-! ## Products over `range n` -/

/-! ### R1. `decide` · closes a closed product of natural numbers
`range n` is the finset `{0, 1, …, n - 1}`; `∏ i ∈ range n, f i` is `f 0 * f 1 * … * f (n - 1)`.
With a numeral `n` and values in `ℕ`, Lean can compute both sides, so `decide` closes it. -/
example : ∏ i ∈ range 3, (2 * i + 1) = 15 := by
  decide

/-! ### R2. `Finset.prod_range_succ` · goal: peel the last factor off a product over `range (n + 1)` -/
example {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P ((∏ x ∈ range n, f x) * f n)) : P (∏ x ∈ range (n + 1), f x) := by
  rw [Finset.prod_range_succ]
  exact h

/-! ### R3. `mul_comm` · goal: `a * b` → `b * a` (the first product `rw` finds) -/
example {M : Type} [CommMonoid M] (a b : M) (P : M → Prop) (h : P (b * a)) : P (a * b) := by
  rw [mul_comm]
  exact h

/-! ### R4. `Finset.prod_const` · goal: a product of a constant → a power, exponent `#s`
`#s` is the number of elements of the finset `s` (`Finset.card s`). -/
example {ι M : Type} [CommMonoid M] (s : Finset ι) (b : M) (P : M → Prop) (h : P (b ^ #s)) :
    P (∏ _x ∈ s, b) := by
  rw [Finset.prod_const]
  exact h

/-! ### R5. `Finset.card_range` · goal: `#(range n)` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P #(range n) := by
  rw [Finset.card_range]
  exact h

/-! ## Sums over all of `Fin n` -/

/-! ### R6. `Fin.sum_univ_three` · goal: `∑ i, f i` over `Fin 3` → three terms
`∑ i, f i` with `f : Fin 3 → M` sums over every `i : Fin 3` (the finset `Finset.univ`). -/
example {M : Type} [AddCommMonoid M] (f : Fin 3 → M) (P : M → Prop) (h : P (f 0 + f 1 + f 2)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_three]
  exact h

/-! ### R7. `Fin.sum_univ_succ` · goal: peel the `0` term off a sum over `Fin (n + 1)`
The rest is a sum over `Fin n`, with every index moved up by one: `i.succ`. -/
example {M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M) (P : M → Prop)
    (h : P (f 0 + ∑ i : Fin n, f i.succ)) : P (∑ i, f i) := by
  rw [Fin.sum_univ_succ]
  exact h

/-! ### R8. `Fin.val_succ` · goal: `↑j.succ` → `↑j + 1`
`↑j` is `(j : ℕ)`, the value of `j : Fin n` as a natural number (`Fin.val j`). -/
example (n : ℕ) (j : Fin n) (P : ℕ → Prop) (h : P (↑j + 1)) : P ↑j.succ := by
  rw [Fin.val_succ]
  exact h

/-! ### R9. `Fin.val_zero` · goal: `↑(0 : Fin (n + 1))` → `0` -/
example (n : ℕ) (P : ℕ → Prop) (h : P 0) : P ↑(0 : Fin (n + 1)) := by
  rw [Fin.val_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Peel, then swap: R2, R3 (the last `rw` closes the goal with `rfl`) -/
example (n : ℕ) :
    ∏ i ∈ range (n + 1), (2 * i + 1) = (2 * n + 1) * ∏ i ∈ range n, (2 * i + 1) := by
  rw [Finset.prod_range_succ]
  rw [mul_comm]

/-! ### W2. A constant product times one more factor: R4, R5, then `pow_succ`
`pow_succ : a ^ (n + 1) = a ^ n * a`; the last `rw` closes the goal with `rfl`. -/
example (n : ℕ) : (∏ _i ∈ range n, (3 : ℤ)) * 3 = 3 ^ (n + 1) := by
  rw [Finset.prod_const]
  rw [Finset.card_range]
  rw [pow_succ]

/-! ### W3. Three terms, then compute: R6, then `decide` on numerals in `ℕ` -/
example : ∑ i : Fin 3, ((i : ℕ) + 1) = 6 := by
  rw [Fin.sum_univ_three]
  decide

/-! ### W4. Peel the `0` term, then `simp` does R8 and R9 -/
example (n : ℕ) : ∑ i : Fin (n + 1), (i : ℕ) = ∑ i : Fin n, ((i : ℕ) + 1) := by
  rw [Fin.sum_univ_succ]
  simp

end E070Guide

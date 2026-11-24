/- Guide for M052 (Geometric sum).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (odd numbers, base 3).
Assumed: Lean basics (E001–E033), in particular `induction` on `ℕ` (E014) and `omega` (E011).
-/
import Mathlib

open Finset

namespace M052Guide

/-! # Part R · Reference entries -/

/-! ## Induction on the upper bound -/

/-! ### R1. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: `P n` → `P 0` and `P (n + 1)`
Each `?_` leaves that case open as a goal, so you can work on it below. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => ?_
    | succ n ih => ?_
  exact h0
  exact hs n ih

/-! ## The base case (`simp` applies these by itself) -/

/-! ### R2. `Finset.sum_range_zero` · `∑ k ∈ range 0, f k = 0` · goal: the empty sum → `0` -/
example {β : Type} [AddCommMonoid β] (f : ℕ → β) (P : β → Prop) (h : P 0) :
    P (∑ i ∈ range 0, f i) := by
  rw [Finset.sum_range_zero]
  exact h

/-! ### R3. `pow_zero` · `a ^ 0 = 1` · goal -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P 1) : P (a ^ 0) := by
  rw [pow_zero]
  exact h

/-! ## The step case -/

/-! ### R4. `Finset.sum_range_succ` · `∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`
goal: peel off the last term. -/
example {β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) (P : β → Prop)
    (h : P (∑ i ∈ range n, f i + f n)) : P (∑ i ∈ range (n + 1), f i) := by
  rw [Finset.sum_range_succ]
  exact h

/-! ### R5. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R6. `omega` · closes linear arithmetic over `ℕ`; any other subterm (here `g n`) is an atom -/
example (s : ℕ) (g : ℕ → ℕ) (n : ℕ) (h : s + 1 = g n) : s + g n + 1 = g n * 2 := by
  omega

/-! ### R7. `mul_add` · `a * (b + c) = a * b + a * c` · goal: distribute -/
example {R : Type} [CommRing R] (a b c : R) (P : R → Prop) (h : P (a * b + a * c)) :
    P (a * (b + c)) := by
  rw [mul_add]
  exact h

/-! ### R8. `ring` · closes an identity of commutative rings, powers `a ^ (n + 1)` with symbolic `n` included -/
example {R : Type} [CommRing R] (a b : R) (n : ℕ) : (a - b) * a ^ n = a ^ (n + 1) - b * a ^ n := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Sum of the first `n` odd numbers: R1, R2–R3 via `simp`, R4, `rw [ih]`, R8 -/
example (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
    | zero => ?_
    | succ n ih => ?_
  · simp
  rw [sum_range_succ]
  rw [ih]
  ring

/-! ### W2. A factor in front of the sum: distribute first (R7) so that `ih` appears literally -/
example (n : ℕ) : 3 * ∑ i ∈ range n, (2 * i + 1) = 3 * n ^ 2 := by
  induction n with
    | zero => ?_
    | succ n ih => ?_
  · simp
  rw [sum_range_succ]
  rw [mul_add]
  rw [ih]
  ring

/-! ### W3. Base 3 over `ℕ`: R4, R5 make the goal linear in two atoms, then R6 -/
example (n : ℕ) : ∑ i ∈ range n, 2 * 3 ^ i + 1 = 3 ^ n := by
  induction n with
    | zero => ?_
    | succ n ih => ?_
  · simp
  rw [sum_range_succ, pow_succ]
  omega

end M052Guide

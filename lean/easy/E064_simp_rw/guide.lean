/- Guide for E064 (simp_rw).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).

Notation used below. `λ x => e` is the same term as `fun x => e` (the infoview prints `fun`);
this folder bans the keyword `fun` in proofs, so the statements here use `λ`. In the infoview
`P fun x => e` means `P (fun x => e)`: Lean drops the parentheses around a trailing `fun`.
-/
import Mathlib

namespace E064Guide

/-! # Part R · Reference entries -/

/-! ## Rewriting under a `fun` binder -/

/-! ### R1. `simp_rw [h]` with `h : ∀ x, g x = k x` · goal: every `g x` under the binder → `k x`
`rw [h]` fails here: the `x` in `g x` is bound by the `fun`, and `rw` cannot match a pattern
against a bound variable. `simp_rw` rewrites under binders. -/
example {ι β : Type} [Add β] (g k : ι → β) (c : β) (h : ∀ x, g x = k x) (P : (ι → β) → Prop)
    (hP : P (λ x => k x + c)) : P (λ x => g x + c) := by
  simp_rw [h]
  exact hP

/-! ### R2. `two_mul` · `2 * a = a + a`; used right to left: `simp_rw [← two_mul]` · goal: `a + a` → `2 * a` -/
example {ι α : Type} [NonAssocSemiring α] (g : ι → α) (P : (ι → α) → Prop)
    (h : P (λ x => 2 * g x)) : P (λ x => g x + g x) := by
  simp_rw [← two_mul]
  exact h

/-! ### R3. `mul_add` · `a * (b + c) = a * b + a * c` · goal: distribute a left factor -/
example {ι α : Type} [Mul α] [Add α] [LeftDistribClass α] (a : α) (g k : ι → α)
    (P : (ι → α) → Prop) (h : P (λ x => a * g x + a * k x)) : P (λ x => a * (g x + k x)) := by
  simp_rw [mul_add]
  exact h

/-! ### R4. `mul_one` · `a * 1 = a` · goal: drop a factor `* 1` -/
example {ι α : Type} [MulOneClass α] [Add α] (g k : ι → α) (P : (ι → α) → Prop)
    (h : P (λ x => g x + k x)) : P (λ x => g x * 1 + k x) := by
  simp_rw [mul_one]
  exact h

/-! ### R5. `simp_rw` closes the goal when it becomes `e = e` or `A ↔ A` · goal list: one goal → none
After each rule, a goal whose two sides are now the same text is closed; nothing is left to write
after the last rule. Sides equal only by computation (`2 * 1` vs `2`) are not closed. -/
example {ι α : Type} (p : α → Prop) (g k : ι → α) (h : ∀ x, g x = k x) :
    (∀ x, p (g x)) ↔ ∀ x, p (k x) := by
  simp_rw [h]

/-! ## Rewriting under `∀` and `∑` -/

/-! ### R6. `zero_add` · `0 + a = a` · goal: under `∀ x`, `0 + x` → `x` -/
example {α : Type} [AddZeroClass α] (p : α → Prop) (Q : Prop → Prop) (h : Q (∀ x, p x)) :
    Q (∀ x, p (0 + x)) := by
  simp_rw [zero_add]
  exact h

/-! ### R7. `simp_rw [two_mul]` under `∑ i ∈ s, …` · goal: each summand `2 * g i` → `g i + g i`
`∑ i ∈ s, e` is `Finset.sum s (fun i => e)`: the summand is a `fun`, so `rw` cannot reach `i`.
`simp_rw` may rename the bound variable (`i` becomes `x`); that changes nothing. -/
example {ι : Type} (s : Finset ι) (g : ι → ℕ) (P : ℕ → Prop) (h : P (∑ i ∈ s, (g i + g i))) :
    P (∑ i ∈ s, 2 * g i) := by
  simp_rw [two_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `rw` does work under a binder when the pattern has no bound variable
Here `c` does not mention `x`, so `rw [h]` finds it. Contrast with R1, where `g x` does. -/
example {ι β : Type} [Add β] (g : ι → β) (c d : β) (h : c = d) (P : (ι → β) → Prop)
    (hP : P (λ x => g x + d)) : P (λ x => g x + c) := by
  rw [h]
  exact hP

/-! ### W2. Nested binders `∃ x, ∀ y`: R4, then R6; the `↔` closes by itself (R5)
One call `simp_rw [mul_one, zero_add]` does the same two steps. -/
example {α : Type} [MulOneClass α] [AddZeroClass α] (p : α → α → Prop) :
    (∃ x, ∀ y, p (x * 1) (0 + y)) ↔ ∃ x, ∀ y, p x y := by
  simp_rw [mul_one]
  simp_rw [zero_add]

/-! ### W3. A chain under `∑`: R4, then R2; the goal closes by itself (R5) -/
example {ι : Type} (s : Finset ι) (g : ι → ℕ) :
    ∑ i ∈ s, (g i * 1 + g i * 1) = ∑ i ∈ s, 2 * g i := by
  simp_rw [mul_one]
  simp_rw [← two_mul]

end E064Guide

/- Guide for M056 (Counting with Finset.filter).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The induction entry uses `induction n with | zero => ?_ | succ k ih => ?_` so that both cases show up
as goals in the infoview; in the exercise you may put the tactics right after each `=>` instead.
Part W: a worked combination on another count (multiples of 3), not on the exercise's.
Assumed: Lean basics (easy tier E001–E033), in particular `induction` on `Nat` (E014).
-/
import Mathlib

open Finset

namespace M056Guide

/-! # Part R · Reference entries -/

/-! ## Splitting `n` into `0` and `k + 1` -/

/-! ### R1. `induction n with | zero => ?_ | succ k ih => ?_` · goal list: one goal → two goals
Case `zero`: `n` is replaced by `0`. Case `succ`: `n` is replaced by `k + 1`, and the context gains
`k` and the induction hypothesis `ih : P k`. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ k ih => ?_
  · exact h0
  · exact hs k ih

/-! ### R2. `simp` · closes a `zero` case of a count: `c * 0 = 0`, `range 0 = ∅`,
`filter p ∅ = ∅`, `#∅ = 0` are all simp lemmas. -/
example (p : ℕ → Prop) [DecidablePred p] (c : ℕ) : (filter p (range (c * 0))).card = 0 := by
  simp

/-! ## Exposing the new elements of the range -/

/-! ### R3. `rw [show a = b by ring]` · goal: an expression → an equal one in the shape a lemma needs
`show a = b by ring` is a proof of `a = b` written on the spot (here by `ring`); `rw` then uses it. -/
example (n : ℕ) (P : ℕ → Prop) (h : P (3 * n + 2 + 1)) : P (3 * (n + 1)) := by
  rw [show 3 * (n + 1) = 3 * n + 2 + 1 by ring]
  exact h

/-! ### R4. `Finset.range_add_one` · `range (n + 1) = insert n (range n)` · goal: the range up to
`n + 1` → the range up to `n` with the new top element `n` inserted -/
example (n : ℕ) (P : Finset ℕ → Prop) (h : P (insert n (range n))) : P (range (n + 1)) := by
  rw [Finset.range_add_one]
  exact h

/-! ## Pushing the filter through `insert` -/

/-! ### R5. `Finset.filter_insert` · goal: `filter p (insert a s)` → an `if` on `p a`
`filter p (insert a s) = if p a then insert a (filter p s) else filter p s` -/
example {α : Type} [DecidableEq α] (p : α → Prop) [DecidablePred p] (a : α) (s : Finset α)
    (P : Finset α → Prop) (h : P (if p a then insert a (filter p s) else filter p s)) :
    P (filter p (insert a s)) := by
  rw [Finset.filter_insert]
  exact h

/-! ## Deciding the parity tests -/

/-! ### R6. `even_two_mul` · `Even (2 * a)` · context gains the fact (via `have`) -/
example {α : Type} [Semiring α] (a : α) (G : Prop) (g : Even (2 * a) → G) : G := by
  have h : Even (2 * a) := even_two_mul a
  exact g h

/-! ### R7. `simp` proves `¬ Even (2 * m + 1)` (simp lemma `Nat.not_even_bit1`) · context gains it -/
example (m : ℕ) (G : Prop) (g : ¬ Even (2 * m + 1) → G) : G := by
  have h : ¬ Even (2 * m + 1) := by simp
  exact g h

/-! ### R8. `simp only [hc, if_true]` (`hc : c`) · goal: `if c then x else y` → `x`
`hc` turns `c` into `True`; `if_true : (if True then t else e) = t` finishes. -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (hc : c) (P : α → Prop) (h : P x) :
    P (if c then x else y) := by
  simp only [hc, if_true]
  exact h

/-! ### R9. `simp only [hc, if_false]` (`hc : ¬ c`) · goal: `if c then x else y` → `y`
`hc` turns `c` into `False`; `if_false : (if False then t else e) = e` finishes. -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (hc : ¬ c) (P : α → Prop) (h : P y) :
    P (if c then x else y) := by
  simp only [hc, if_false]
  exact h

/-! ## Counting the inserted element -/

/-! ### R10. `Finset.card_insert_of_notMem` · `a ∉ s → #(insert a s) = #s + 1`
· goal list: goal rewritten, plus side goal `a ∉ s`
Write `rw [Finset.card_insert_of_notMem (by simp)]` to close the side goal on the spot. -/
example {α : Type} [DecidableEq α] (a : α) (s : Finset α) (P : ℕ → Prop) (h : P (s.card + 1))
    (ha : a ∉ s) : P (insert a s).card := by
  rw [Finset.card_insert_of_notMem]
  exact h
  exact ha

/-! ### R11. `Finset.mem_filter` · `a ∈ filter p s ↔ a ∈ s ∧ p a` · goal: membership in a filter
→ membership in `s` and the test -/
example {α : Type} (p : α → Prop) [DecidablePred p] (a : α) (s : Finset α)
    (h : ¬ (a ∈ s ∧ p a)) : a ∉ filter p s := by
  rw [Finset.mem_filter]
  exact h

/-! ### R12. `Finset.mem_range` · `m ∈ range n ↔ m < n` · goal: membership in a range → `<` -/
example (m n : ℕ) (P : Prop → Prop) (h : P (m < n)) : P (m ∈ range n) := by
  rw [Finset.mem_range]
  exact h

/-! ### R13. `simp` · closes `a ∉ filter p (range a)`: R11, R12, then `a < a` is false
(`lt_self_iff_false`). This is the side goal of R10 in the exercise. -/
example (p : ℕ → Prop) [DecidablePred p] (a : ℕ) : a ∉ filter p (range a) := by
  simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Exactly `n` of `0, 1, …, 3n - 1` are multiples of 3. R1; R2 for `zero`; for `succ`: R3,
R4 three times, R5 three times, R6/R7-style facts (here by `omega`), R8/R9, R10 with R13, `rw [ih]`. -/
example (n : ℕ) : (filter (fun m => 3 ∣ m) (range (3 * n))).card = n := by
  induction n with | zero => ?_ | succ k ih => ?_
  · simp
  rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring]
  rw [Finset.range_add_one, Finset.range_add_one, Finset.range_add_one]
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert]
  have h0 : 3 ∣ 3 * k := by omega
  have h1 : ¬ 3 ∣ 3 * k + 1 := by omega
  have h2 : ¬ 3 ∣ 3 * k + 2 := by omega
  simp only [h0, h1, h2, if_true, if_false]
  rw [Finset.card_insert_of_notMem (by simp)]
  rw [ih]

end M056Guide

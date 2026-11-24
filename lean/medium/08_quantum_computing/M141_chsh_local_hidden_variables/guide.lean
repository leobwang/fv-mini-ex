/- Guide for M141 (CHSH inequality for local hidden variables).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (two ±1 values, one weighted sum).
Assumed: Lean basics.
-/
import Mathlib

namespace M141Guide

/-! # Part R · Reference entries -/

/-! ## The pointwise bound: case split on ±1 values -/

/-! ### R1. `rcases h with h | h` · goal list: one goal per side of `∨`; context: `h` is replaced -/
example (a : ℝ) (P : ℝ → Prop) (ha : a = 1 ∨ a = -1) (h1 : P 1) (h2 : P (-1)) : P a := by
  rcases ha with h | h
  · rw [h]; exact h1
  · rw [h]; exact h2

/-! ### R2. `rcases ha with h | h <;> rcases hb with h' | h'` · goal list: 2 × 2 = 4 goals
`t <;> u` runs `u` on every goal `t` leaves, so each further `<;> rcases` doubles the goal count. -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hP : ∀ x y : ℝ, P x y) : P a b := by
  rcases ha with h | h <;> rcases hb with h' | h'
  all_goals exact hP _ _

/-! ### R3. `abs_le` · `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b` · goal: an `|·|` bound → two inequalities -/
example (a b : ℝ) (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := by
  rw [abs_le]
  exact h

/-! ### R4. `norm_num [abs_le]` · closes a numeric `|·| ≤ ·` goal
`norm_num` evaluates the numerals; the extra lemma `abs_le` (R3) turns `|x| ≤ b` into
`-b ≤ x ∧ x ≤ b`, which `norm_num` then decides. -/
example : |(1 : ℝ) * -1 + -1 * 1 + 3| ≤ 2 := by
  norm_num [abs_le]

/-! ## Averaging over the hidden variable -/

/-! ### R5. `calc` · goal list: `a ≤ c` → one goal per step; `_` on the first line is the goal's left side
`≤` followed by `=` chains to `≤`. Normally each `?_` is a proof term written right there. -/
example (a b c : ℝ) (hab : a ≤ b) (hbc : b = c) : a ≤ c := by
  calc _ ≤ b := ?_
    _ = c := ?_
  exacts [hab, hbc]

/-! ### R6. `Finset.abs_sum_le_sum_abs` · `|∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|` · closes the goal
The triangle inequality for finite sums. `∑ i, f i` is the sum over all of `ι` (`Finset.univ`). -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) : |∑ i, f i| ≤ ∑ i, |f i| := by
  exact Finset.abs_sum_le_sum_abs _ _

/-! ### R7. `Finset.sum_congr rfl` · goal: `∑ f = ∑ g` → `∀ x ∈ univ, f x = g x`; then `intro i _` -/
example {ι : Type} [Fintype ι] (f g : ι → ℝ) (h : ∀ i, f i = g i) : ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  exact h i

/-! ### R8. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R9. `abs_of_nonneg` · `0 ≤ a → |a| = a` · goal: `|a|` → `a` -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_nonneg ha]
  exact h

/-! ### R10. `Finset.sum_le_sum` · goal: `∑ f ≤ ∑ g` → `∀ i ∈ univ, f i ≤ g i`; then `intro i _` -/
example {ι : Type} [Fintype ι] (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) : ∑ i, f i ≤ ∑ i, g i := by
  refine Finset.sum_le_sum ?_
  intro i _
  exact h i

/-! ### R11. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · goal list: two goals -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c := by
  apply mul_le_mul_of_nonneg_left
  exacts [hbc, ha]

/-! ### R12. `Finset.sum_mul` · `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; right to left factors `a` out -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) * a)) :
    P (∑ i, f i * a) := by
  rw [← Finset.sum_mul]
  exact h

/-! ### R13. `one_mul` · `1 * a = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Two ±1 values, four cases: R2, then `rw [h, h']`, then R4 -/
example (a b : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : |a + a * b| ≤ 2 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h']
  all_goals norm_num [abs_le]

/-! ### W2. A weighted average of values in `[-1, 1]` stays in `[-1, 1]`: R5 with R6, R7–R9, R10–R11, R12–R13
Steps 2 and 3 are term-mode: `fun i _ => …` takes the index and the (unused) proof of `i ∈ univ`. -/
example {ι : Type} [Fintype ι] (q s : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1)
    (hs : ∀ i, |s i| ≤ 1) : |∑ i, q i * s i| ≤ 1 := by
  calc _ ≤ ∑ i, |q i * s i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, q i * |s i| := Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (hq i)]
    _ ≤ ∑ i, q i * 1 := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hs i) (hq i)
    _ = 1 := by rw [← Finset.sum_mul, hsum, one_mul]

end M141Guide

/- Guide for M080 (The union bound).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace M080Guide

/-! # Part R · Reference entries -/

/-! ## Induction on a finite set -/

/-! ### R1. `classical` · context: every proposition becomes decidable; goal unchanged
`insert a s` on `Finset ι` needs `DecidableEq ι` (to drop a duplicate `a`). `classical` supplies it,
and any other `Decidable` instance, for the rest of the proof. Here it lets `if h : a = b` compile. -/
example {ι : Type} (a b : ι) : a = b ∨ a ≠ b := by
  classical
  exact if h : a = b then Or.inl h else Or.inr h

/-! ### R2. `induction s using Finset.induction_on with …` · goal list: `P s` → `P ∅` and `P (insert a s)`
The second case gets `a : ι`, the smaller set `s`, `ha : a ∉ s` and the hypothesis `ih : P s`.
Writing `?_` after `=>` leaves a case as a goal; normally you write its proof there. -/
example {ι : Type} [DecidableEq ι] (P : Finset ι → Prop) (h0 : P ∅)
    (hi : ∀ a s, a ∉ s → P s → P (insert a s)) (s : Finset ι) : P s := by
  induction s using Finset.induction_on with
    | empty => ?_
    | insert a s ha ih => ?_
  exact h0
  exact hi a s ha ih

/-! ## The empty case (`simp` applies R3–R5 by itself) -/

/-! ### R3. `Finset.sum_empty` · goal: `∑ i ∈ ∅, f i` → `0` -/
example {ι : Type} (f : ι → ℝ≥0∞) (P : ℝ≥0∞ → Prop) (h : P 0) : P (∑ i ∈ ∅, f i) := by
  rw [Finset.sum_empty]
  exact h

/-! ### R4. The empty bounded union · goal: `⋃ i ∈ (∅ : Finset ι), t i` → `∅`
`⋃ i ∈ s, t i` is `⋃ i, ⋃ (_ : i ∈ s), t i`. `Finset.notMem_empty` makes `i ∈ ∅` into `False`,
`Set.iUnion_of_empty` empties a union over the proofs of `False`, `Set.iUnion_empty` drops `⋃ i, ∅`. -/
example {Ω ι : Type} (t : ι → Set Ω) (P : Set Ω → Prop) (h : P ∅) :
    P (⋃ i ∈ (∅ : Finset ι), t i) := by
  simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
  exact h

/-! ### R5. `measure_empty` · goal: `μ ∅` → `0` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (P : ℝ≥0∞ → Prop) (h : P 0) : P (μ ∅) := by
  rw [measure_empty]
  exact h

/-! ## The insert case: split off one element -/

/-! ### R6. `Finset.set_biUnion_insert` · goal: `⋃ x ∈ insert a s, t x` → `t a ∪ ⋃ x ∈ s, t x` -/
example {Ω ι : Type} [DecidableEq ι] (a : ι) (s : Finset ι) (t : ι → Set Ω) (P : Set Ω → Prop)
    (h : P (t a ∪ ⋃ x ∈ s, t x)) : P (⋃ x ∈ insert a s, t x) := by
  rw [Finset.set_biUnion_insert]
  exact h

/-! ### R7. `Finset.sum_insert ha` · `a ∉ s → ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x` · goal -/
example {ι : Type} [DecidableEq ι] (a : ι) (s : Finset ι) (ha : a ∉ s) (f : ι → ℝ≥0∞)
    (P : ℝ≥0∞ → Prop) (h : P (f a + ∑ x ∈ s, f x)) : P (∑ x ∈ insert a s, f x) := by
  rw [Finset.sum_insert ha]
  exact h

/-! ## Chaining inequalities -/

/-! ### R8. `measure_union_le` · closes `μ (s ∪ t) ≤ μ s + μ t` (subadditivity for two sets)
No measurability is needed. Both sets are explicit arguments: `measure_union_le s t`, or `_ _`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) : μ (s ∪ t) ≤ μ s + μ t := by
  exact measure_union_le s t

/-! ### R9. `le_trans` as `hab.trans` · goal `a ≤ c` → `b ≤ c`, given `hab : a ≤ b` -/
example {α : Type} [Preorder α] (a b c : α) (hab : a ≤ b) (h : b ≤ c) : a ≤ c := by
  refine hab.trans ?_
  exact h

/-! ### R10. `add_le_add` · goal `a + c ≤ b + d` → `a ≤ b` and `c ≤ d` -/
example (a b c d : ℝ≥0∞) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  refine add_le_add ?_ ?_
  exact hab
  exact hcd

/-! ### R11. `le_rfl` · closes `a ≤ a` (the arguments are implicit: Lean reads `a` off the goal) -/
example {α : Type} [Preorder α] (a : α) : a ≤ a := by
  exact le_rfl

/-! ## The uniform corollary -/

/-! ### R12. `calc` · closes `a ≤ c` from a chain of steps; `≤` and `=` steps may be mixed
Each line `_ ≤ x := proof` starts from the previous right side. A proof can be `by tac`. -/
example {α : Type} [Preorder α] (a b c : α) (hab : a ≤ b) (hbc : b = c) : a ≤ c := by
  calc a ≤ b := hab
    _ = c := hbc

/-! ### R13. `Finset.sum_le_sum` · goal `∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` → `∀ i ∈ s, f i ≤ g i`
As a term: `Finset.sum_le_sum h` with `h : ∀ i ∈ s, f i ≤ g i`; `g` may be a constant `fun _ => c`. -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ≥0∞) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  apply Finset.sum_le_sum
  exact h

/-! ### R14. `Finset.sum_const` · goal: `∑ _x ∈ s, b` → `s.card • b` (`•`: repeated addition, `n • b = b + … + b`) -/
example {ι : Type} (s : Finset ι) (b : ℝ≥0∞) (P : ℝ≥0∞ → Prop) (h : P (s.card • b)) :
    P (∑ _x ∈ s, b) := by
  rw [Finset.sum_const]
  exact h

/-! ### R15. `nsmul_eq_mul` · `n • a = ↑n * a` · goal: `n • a` → the cast `↑n` times `a` -/
example (n : ℕ) (a : ℝ≥0∞) (P : ℝ≥0∞ → Prop) (h : P (↑n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Induction with the insert step done by R7 and R10: a sum grows when each term grows -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ≥0∞) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, (f i + g i) := by
  classical
  induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add le_self_add ih

/-! ### W2. Three sets: R8 twice, glued by R9, R10, R11 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t u : Set Ω) :
    μ (s ∪ t ∪ u) ≤ μ s + μ t + μ u := by
  refine (measure_union_le _ _).trans ?_
  exact add_le_add (measure_union_le _ _) le_rfl

/-! ### W3. A constant sum as a product: R14, R15, then `mul_comm` -/
example {ι : Type} (s : Finset ι) : ∑ _i ∈ s, (2 : ℝ≥0∞) = 2 * s.card := by
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [mul_comm]

end M080Guide

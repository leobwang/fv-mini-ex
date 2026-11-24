/- Guide for M081 (Total probability and Bayes).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

open ProbabilityTheory MeasureTheory
open scoped ENNReal

namespace M081Guide

/-! # Part R · Reference entries -/

/-! ## Conditional probability times probability = probability of the intersection -/

/-! ### R1. `ProbabilityTheory.cond_mul_eq_inter` · goal: `μ[t | s] * μ s` → `μ (s ∩ t)`
`μ[t | s]` is `cond μ s t`, the probability of `t` given `s`. Needs `hs : MeasurableSet s`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω)
    (hs : MeasurableSet s) (P : ℝ≥0∞ → Prop) (h : P (μ (s ∩ t))) : P (μ[t | s] * μ s) := by
  rw [cond_mul_eq_inter hs]
  exact h

/-! ### R2. `simp_rw [cond_mul_eq_inter (hs _)]` · goal: the same rewrite inside every term of a `∑ i`
`rw` cannot rewrite a term that mentions the bound variable `i`; `simp_rw` can. `(hs _)` lets Lean
choose `i` separately in each term. -/
example {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i)) (t : Set Ω) (P : ℝ≥0∞ → Prop)
    (h : P (∑ i, μ (s i ∩ t))) : P (∑ i, μ[t | s i] * μ (s i)) := by
  simp_rw [cond_mul_eq_inter (hs _)]
  exact h

/-! ## Set algebra for the cover -/

/-! ### R3. `Set.iUnion_inter` · `(⋃ i, t i) ∩ s = ⋃ i, t i ∩ s`; right to left: `rw [← Set.iUnion_inter]` -/
example {Ω ι : Type} (t : ι → Set Ω) (s : Set Ω) (P : Set Ω → Prop) (h : P ((⋃ i, t i) ∩ s)) :
    P (⋃ i, t i ∩ s) := by
  rw [← Set.iUnion_inter]
  exact h

/-! ### R4. `Set.univ_inter` · `Set.univ ∩ s = s` · goal: drop the whole space from an intersection -/
example {Ω : Type} (s : Set Ω) (P : Set Ω → Prop) (h : P s) : P (Set.univ ∩ s) := by
  rw [Set.univ_inter]
  exact h

/-! ### R5. `conv_lhs => rw [ha]` · goal `F a = G a` → `F b = G a`: rewrite the left side only
`rw [ha]` would rewrite every `a`, on both sides and inside `b` too. -/
example {α β : Type} (a b : α) (F G : α → β) (ha : a = b) (h : F b = G a) : F a = G a := by
  conv_lhs => rw [ha]
  exact h

/-! ## Countable additivity -/

/-! ### R6. `MeasureTheory.measure_iUnion` · goal list: `μ (⋃ i, f i)` → `∑' i, μ (f i)`, plus two side goals
`∑'` is an infinite sum (`tsum`). The side goals: the `f i` are pairwise disjoint, and each is
measurable. Pass both proofs as arguments, `rw [measure_iUnion hd hm]`, to avoid the side goals. -/
example {Ω ι : Type} [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω) (f : ι → Set Ω)
    (P : ℝ≥0∞ → Prop) (h : P (∑' i, μ (f i))) (hd : Pairwise (Function.onFun Disjoint f))
    (hm : ∀ i, MeasurableSet (f i)) : P (μ (⋃ i, f i)) := by
  rw [measure_iUnion]
  exact h
  exact hd
  exact hm

/-! ### R7. `intro i j hij` on `Pairwise R` · context gains `i j : ι` and `hij : i ≠ j`
`Pairwise R` means `∀ ⦃i j⦄, i ≠ j → R i j`; `Function.onFun Disjoint f i j` is `Disjoint (f i) (f j)`.
So `hd hij : Disjoint (f i) (f j)` when `hd : Pairwise (Function.onFun Disjoint f)`. -/
example {Ω ι : Type} (f : ι → Set Ω) (h : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    Pairwise (Function.onFun Disjoint f) := by
  intro i j hij
  exact h i j hij

/-! ### R8. `Disjoint.mono` · goal `Disjoint a c` → `a ⊆ b` and `c ⊆ d`, from `hbd : Disjoint b d`
Shrinking two disjoint sets keeps them disjoint. The lemma is stated with `≤`, which on sets is `⊆`.
Written as a term: `hbd.mono hab hcd`. -/
example {Ω : Type} (a b c d : Set Ω) (hbd : Disjoint b d) (hab : a ⊆ b) (hcd : c ⊆ d) :
    Disjoint a c := by
  refine hbd.mono ?_ ?_
  exact hab
  exact hcd

/-! ### R9. `Set.inter_subset_left` · closes `s ∩ t ⊆ s` (`s`, `t` implicit: Lean reads them off the goal) -/
example {Ω : Type} (s t : Set Ω) : s ∩ t ⊆ s := by
  exact Set.inter_subset_left

/-! ### R10. `MeasurableSet.inter` · goal `MeasurableSet (s ∩ t)` → `MeasurableSet s`, `MeasurableSet t`
As a term: `hs.inter ht`. -/
example {Ω : Type} [MeasurableSpace Ω] (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ t) := by
  apply MeasurableSet.inter
  exact hs
  exact ht

/-! ### R11. `tsum_fintype` · goal: `∑' i, f i` over a finite type → the finite sum `∑ i, f i` -/
example {ι : Type} [Fintype ι] (f : ι → ℝ≥0∞) (P : ℝ≥0∞ → Prop) (h : P (∑ i, f i)) :
    P (∑' i, f i) := by
  rw [tsum_fintype]
  exact h

/-! ## Bayes: turning the conditional around -/

/-! ### R12. `ProbabilityTheory.cond_eq_inv_mul_cond_mul` · goal: `μ[t | s]` → `(μ s)⁻¹ * μ[s | t] * μ t`
Needs `hs : MeasurableSet s` and `ht : MeasurableSet t`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (P : ℝ≥0∞ → Prop)
    (h : P ((μ s)⁻¹ * μ[s | t] * μ t)) : P μ[t | s] := by
  rw [cond_eq_inv_mul_cond_mul hs ht]
  exact h

/-! ### R13. `div_eq_mul_inv` · `a / b = a * b⁻¹` · goal: division → multiplication by an inverse -/
example (a b : ℝ≥0∞) (P : ℝ≥0∞ → Prop) (h : P (a * b⁻¹)) : P (a / b) := by
  rw [div_eq_mul_inv]
  exact h

/-! ### R14. `ring` in `ℝ≥0∞` · closes a commutative-semiring identity; `x⁻¹` is treated as an unknown -/
example (a b c : ℝ≥0∞) : a⁻¹ * b * c = c * b * a⁻¹ := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Disjointness survives intersecting with a fixed set on the left: R7, R8, then `inter_subset_right` -/
example {Ω ι : Type} (t : ι → Set Ω) (hd : Pairwise (Function.onFun Disjoint t)) (s : Set Ω) :
    Pairwise (Function.onFun Disjoint fun i => s ∩ t i) := by
  intro i j hij
  exact (hd hij).mono Set.inter_subset_right Set.inter_subset_right

/-! ### W2. Two disjoint measurable pieces: R6 with its arguments, R11, then `Fin.sum_univ_two` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Fin 2 → Set Ω)
    (hd : Pairwise (Function.onFun Disjoint f)) (hm : ∀ i, MeasurableSet (f i)) :
    μ (⋃ i, f i) = μ (f 0) + μ (f 1) := by
  rw [measure_iUnion hd hm]
  rw [tsum_fintype]
  rw [Fin.sum_univ_two]

/-! ### W3. Division and reordering in `ℝ≥0∞`: R13, then R14 -/
example (a b c : ℝ≥0∞) : a * b / c = c⁻¹ * b * a := by
  rw [div_eq_mul_inv]
  ring

end M081Guide

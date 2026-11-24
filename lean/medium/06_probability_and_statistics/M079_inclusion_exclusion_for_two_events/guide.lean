/- Guide for M079 (Inclusion–exclusion for two events).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace M079Guide

/-! # Part R · Reference entries -/

/-! ## Sets: cutting a union into disjoint pieces -/

/-! ### R1. `rw [← Set.union_sdiff_self]` · goal: `s ∪ t` → `s ∪ t \ s`
`Set.union_sdiff_self : s ∪ t \ s = s ∪ t`; `\` binds tighter than `∪`, so the left side is
`s ∪ (t \ s)`. Right to left it replaces the first `_ ∪ _` in the goal. -/
example {α : Type} (s t : Set α) (P : Set α → Prop) (h : P (s ∪ t \ s)) : P (s ∪ t) := by
  rw [← Set.union_sdiff_self]
  exact h

/-! ### R2. `Set.disjoint_sdiff_right` · closes `Disjoint s (t \ s)`
`s` and `t \ s` share no point. `s` and `t` are implicit: Lean reads them off the goal. -/
example {α : Type} (s t : Set α) : Disjoint s (t \ s) := by
  exact Set.disjoint_sdiff_right

/-! ## Measurability and measures -/

/-! ### R3. `MeasurableSet.diff` · closes `MeasurableSet (t \ s)`
`MeasurableSet.diff : MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)`.
`ht.diff hs` is dot notation for `MeasurableSet.diff ht hs` (because `ht : MeasurableSet t`). -/
example {Ω : Type} [MeasurableSpace Ω] (s t : Set Ω) (hs : MeasurableSet s)
    (ht : MeasurableSet t) : MeasurableSet (t \ s) := by
  exact ht.diff hs

/-! ### R4. `rw [measure_union hd ht]` · goal: `μ (s ∪ t)` → `μ s + μ t`
`measure_union : Disjoint s₁ s₂ → MeasurableSet s₂ → μ (s₁ ∪ s₂) = μ s₁ + μ s₂`.
Both hypotheses are passed as arguments, so `rw` adds no side goal. Only the SECOND set needs
to be measurable. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (hd : Disjoint s t)
    (ht : MeasurableSet t) (P : ℝ≥0∞ → Prop) (h : P (μ s + μ t)) : P (μ (s ∪ t)) := by
  rw [measure_union hd ht]
  exact h

/-! ### R5. `rw [measure_inter_add_sdiff s ht]` · goal: `μ (s ∩ t) + μ (s \ t)` → `μ s`
`measure_inter_add_sdiff (s) : MeasurableSet t → μ (s ∩ t) + μ (s \ t) = μ s`: cutting `s` by
a measurable `t`. `s` is an explicit argument, `t` is read off `ht`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (ht : MeasurableSet t)
    (P : ℝ≥0∞ → Prop) (h : P (μ s)) : P (μ (s ∩ t) + μ (s \ t)) := by
  rw [measure_inter_add_sdiff s ht]
  exact h

/-! ## Equations -/

/-! ### R6. `e.symm` (`Eq.symm`) · context gains the flipped equation
`Eq.symm : a = b → b = a`. Write it as `e.symm` for any proof `e : a = b`. -/
example {α : Type} (a b : α) (e : a = b) (G : Prop) (g : b = a → G) : G := by
  have h : b = a := e.symm
  exact g h

/-! ### R7. `rw [Set.inter_comm s t]` · goal: `s ∩ t` → `t ∩ s`
`Set.inter_comm (a b : Set α) : a ∩ b = b ∩ a`. Without arguments, `rw [Set.inter_comm]`
swaps the first `_ ∩ _` it meets (and every copy of that same intersection). -/
example {α : Type} (s t : Set α) (P : Set α → Prop) (h : P (t ∩ s)) : P (s ∩ t) := by
  rw [Set.inter_comm s t]
  exact h

/-! ### R8. `ring` · closes an identity of `+` and `*` in `ℝ≥0∞` (a commutative semiring)
It treats every `μ (…)` as an unknown. It does not subtract (`ℝ≥0∞` has only truncated `-`). -/
example (a b c : ℝ≥0∞) : a + b + c = b + (c + a) := by
  ring

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. The mirror cut `s ∪ t = (s \ t) ∪ t`: rewrite the union, then additivity
`Set.sdiff_union_self : s \ t ∪ t = s ∪ t`, `Set.disjoint_sdiff_left : Disjoint (t \ s) s`.
After the second `rw` both sides are equal and `rw` closes the goal by itself. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (ht : MeasurableSet t) :
    μ (s ∪ t) = μ (s \ t) + μ t := by
  rw [← Set.sdiff_union_self]
  rw [measure_union Set.disjoint_sdiff_left ht]

/-! ### W2. Flip R5 into a fact, rewrite with it, rearrange with `ring`: R5, R6, `rw`, R8 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t u : Set Ω) (ht : MeasurableSet t) :
    μ u + μ s = μ (s \ t) + μ u + μ (s ∩ t) := by
  have h : μ s = μ (s ∩ t) + μ (s \ t) := (measure_inter_add_sdiff s ht).symm
  rw [h]
  ring

end M079Guide

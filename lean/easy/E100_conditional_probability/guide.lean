/- Guide for E100 (Conditional probability).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a number `a⁻¹ * (a * x)`, the event
`s` conditioned on itself).
Assumed: Lean basics, and E095 (measures, events, `ENNReal`).
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace E100Guide

/-! # Part R · Reference entries -/

/-! ## Unfolding the conditional probability -/

/-! ### R1. `cond_apply` · `MeasurableSet s → μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)` · goal
`μ[t | s]` is notation (from `open ProbabilityTheory`) for `cond μ s t`: the measure `μ` conditioned on
`s`, evaluated at `t`. Only `s` must be measurable. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (hs : MeasurableSet s)
    (P : ENNReal → Prop) (h : P ((μ s)⁻¹ * μ (s ∩ t))) : P μ[t | s] := by
  rw [cond_apply hs]
  exact h

/-! ## Algebra in `ENNReal` (no `ring`: `ENNReal` is not a ring) -/

/-! ### R2. `mul_assoc` · `a * b * c = a * (b * c)`; right to left: `rw [← mul_assoc]` · goal
`*` groups to the left, so `a * b * c` is `(a * b) * c`. -/
example {α : Type} [Monoid α] (a b c : α) (P : α → Prop) (h : P (a * b * c)) :
    P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R3. `measure_ne_top` · `μ s ≠ ⊤` for a finite measure · closes the goal
`⊤` ("top") is how `∞ : ENNReal` prints. `[IsProbabilityMeasure μ]` gives `[IsFiniteMeasure μ]`.
Both `μ` and `s` are explicit: `measure_ne_top μ s`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) :
    μ s ≠ ⊤ := by
  exact measure_ne_top μ s

/-! ### R4. `ENNReal.inv_mul_cancel` · `a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1` · goal
Both side conditions are explicit arguments: `ENNReal.inv_mul_cancel ha0 hatop`. -/
example (a : ENNReal) (ha0 : a ≠ 0) (hatop : a ≠ ⊤) (P : ENNReal → Prop) (h : P 1) :
    P (a⁻¹ * a) := by
  rw [ENNReal.inv_mul_cancel ha0 hatop]
  exact h

/-! ### R5. `one_mul` · `1 * a = a` · goal -/
example {α : Type} [Monoid α] (a : α) (P : α → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Cancelling a factor in `ENNReal`: R2 → R4 → R5
`rw` tries `rfl` after rewriting, so the last `rw` closes `x = x`. -/
example (a x : ENNReal) (ha0 : a ≠ 0) (hatop : a ≠ ⊤) : a⁻¹ * (a * x) = x := by
  rw [← mul_assoc]
  rw [ENNReal.inv_mul_cancel ha0 hatop]
  rw [one_mul]

/-! ### W2. An event conditioned on itself: R1, then `Set.inter_self : s ∩ s = s`, then R4 with R3 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hs : MeasurableSet s) (hs0 : μ s ≠ 0) : μ[s | s] = 1 := by
  rw [cond_apply hs]
  rw [Set.inter_self]
  rw [ENNReal.inv_mul_cancel hs0 (measure_ne_top μ s)]

end E100Guide

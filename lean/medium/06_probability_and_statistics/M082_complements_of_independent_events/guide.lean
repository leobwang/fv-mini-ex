/- Guide for M082 (Complements of independent events).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics. Names used below: `Ω` a sample space, `μ : Measure Ω` a measure, `s t : Set Ω`
events; `μ s : ENNReal` is the measure of `s`, a value in `[0, ∞]` (`⊤` is `∞`).
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M082Guide

/-! # Part R · Reference entries -/

/-! ## Independence ↔ a product equation -/

/-! ### R1. `indepSet_iff_measure_inter_eq_mul hs ht μ` · goal: `IndepSet s t μ` → `μ (s ∩ t) = μ s * μ t`
Needs both events measurable. Pass `μ` explicitly: it is an `autoParam` defaulting to `volume`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (h : μ (s ∩ t) = μ s * μ t) :
    IndepSet s t μ := by
  rw [indepSet_iff_measure_inter_eq_mul hs ht μ]
  exact h

/-! ### R2. `ht.compl` (lemma `MeasurableSet.compl`) · context gains `MeasurableSet tᶜ` -/
example {Ω : Type} [MeasurableSpace Ω] (t : Set Ω) (ht : MeasurableSet t) (G : Prop)
    (g : MeasurableSet tᶜ → G) : G := by
  have htc : MeasurableSet tᶜ := ht.compl
  exact g htc

/-! ### R3. `rw [lemma] at h` · context: the type of `h` is rewritten; goal unchanged -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (h : IndepSet s t μ) :
    μ (s ∩ t) = μ s * μ t := by
  rw [indepSet_iff_measure_inter_eq_mul hs ht μ] at h
  exact h

/-! ## Splitting an event and cancelling in `ENNReal` -/

/-! ### R4. `measure_inter_add_sdiff` · `μ (s ∩ t) + μ (s \ t) = μ s`; `rw [← …]` splits `μ s` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (ht : MeasurableSet t)
    (P : ENNReal → Prop) (h : P (μ (s ∩ t) + μ (s \ t))) : P (μ s) := by
  rw [← measure_inter_add_sdiff s ht]
  exact h

/-! ### R5. `measure_ne_top μ s` · context gains `μ s ≠ ⊤` (any finite measure, so any probability) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (G : Prop) (g : μ s ≠ ⊤ → G) : G := by
  have hs : μ s ≠ ⊤ := measure_ne_top μ s
  exact g hs

/-! ### R6. `ENNReal.add_sub_cancel_left ha` · `a ≠ ⊤ → a + b - a = b` · goal -/
example (a b : ENNReal) (ha : a ≠ ⊤) (P : ENNReal → Prop) (h : P b) : P (a + b - a) := by
  rw [ENNReal.add_sub_cancel_left ha]
  exact h

/-! ### R7. `Set.sdiff_eq` · `s \ t = s ∩ tᶜ` · goal -/
example {Ω : Type} (s t : Set Ω) (P : Set Ω → Prop) (h : P (s ∩ tᶜ)) : P (s \ t) := by
  rw [Set.sdiff_eq]
  exact h

/-! ## Complements and distributing -/

/-! ### R8. `prob_compl_eq_one_sub ht` · `μ tᶜ = 1 - μ t` (probability measure) · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (t : Set Ω)
    (ht : MeasurableSet t) (P : ENNReal → Prop) (h : P (1 - μ t)) : P (μ tᶜ) := by
  rw [prob_compl_eq_one_sub ht]
  exact h

/-! ### R9. `ENNReal.mul_sub hc` · `(0 < c → c < b → a ≠ ⊤) → a * (b - c) = a * b - a * c` · goal
Give the side condition as `(fun _ _ => ha)` when you already have `ha : a ≠ ⊤`. -/
example (a b c : ENNReal) (ha : a ≠ ⊤) (P : ENNReal → Prop) (h : P (a * b - a * c)) :
    P (a * (b - c)) := by
  rw [ENNReal.mul_sub (fun _ _ => ha)]
  exact h

/-! ### R10. `mul_one` · `a * 1 = a` · goal -/
example (a : ENNReal) (P : ENNReal → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R11. `rw` closes `x = x` by itself · goal list: the goal disappears
After rewriting, `rw` tries `rfl`; when both sides became the same text the goal is closed. -/
example (a b : ENNReal) (h : a = b) : a * 1 = b := by
  rw [mul_one, h]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Split `μ s` along `t`, written with a complement: R7 (right to left), then R4 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (ht : MeasurableSet t) :
    μ (s ∩ t) + μ (s ∩ tᶜ) = μ s := by
  rw [← Set.sdiff_eq]
  rw [measure_inter_add_sdiff s ht]

/-! ### W2. Any event is independent of the sure event `Set.univ`: R1, then `simp` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hs : MeasurableSet s) : IndepSet s Set.univ μ := by
  rw [indepSet_iff_measure_inter_eq_mul hs MeasurableSet.univ μ]
  simp

/-! ### W3. Cancelling a finite measure: R5 then R6 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (b : ENNReal) : μ s + b - μ s = b := by
  have hs : μ s ≠ ⊤ := measure_ne_top μ s
  rw [ENNReal.add_sub_cancel_left hs]

end M082Guide

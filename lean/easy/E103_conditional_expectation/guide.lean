/- Guide for E103 (Conditional expectation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a finite measure, a constant).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory

namespace E103Guide

/-! # Part R · Reference entries -/

/-! ## The hidden instance argument -/

/-! ### R1. `infer_instance` · closes `SigmaFinite (μ.trim hm)`
R2 and R4 take this as an instance argument `[SigmaFinite (μ.trim hm)]`: `μ` restricted to the
coarser σ-algebra `m` must be σ-finite. For a probability (or any finite) measure Lean finds it
by itself; this entry only shows that it does. -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : SigmaFinite (μ.trim hm) := by
  infer_instance

/-! ## Averaging the conditional expectation -/

/-! ### R2. `MeasureTheory.integral_condExp hm` · goal: `∫ x, μ[f | m] x ∂μ` → `∫ x, f x ∂μ` -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [SigmaFinite (μ.trim hm)] (f : Ω → ℝ) (P : ℝ → Prop) (h : P (∫ x, f x ∂μ)) :
    P (∫ x, (μ[f | m]) x ∂μ) := by
  rw [integral_condExp hm]
  exact h

/-! ## Conditioning on information you already have -/

/-! ### R3. `Measurable.stronglyMeasurable` · context gains `StronglyMeasurable[m] f`
From `hf : Measurable[m] f`, the term `hf.stronglyMeasurable` (dot notation) proves
`StronglyMeasurable[m] f`; the σ-algebra `m` is carried along. The infoview prints both without `[m]`. -/
example {Ω : Type} {m : MeasurableSpace Ω} (f : Ω → ℝ) (hf : Measurable[m] f) (P : Prop)
    (h : StronglyMeasurable[m] f → P) : P := by
  have hs := hf.stronglyMeasurable
  exact h hs

/-! ### R4. `MeasureTheory.condExp_of_stronglyMeasurable hm` · goal `μ[f | m] = f` → two goals
`apply` leaves the lemma's two hypotheses as goals `case hf` and `case hfi`. -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [SigmaFinite (μ.trim hm)] (f : Ω → ℝ) (hs : StronglyMeasurable[m] f) (hi : Integrable f μ) :
    μ[f | m] = f := by
  apply condExp_of_stronglyMeasurable hm
  exact hs
  exact hi

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R2 inside a larger goal, for a finite measure (R1 still finds the instance) -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → ℝ) : ∫ x, (μ[f | m]) x ∂μ - ∫ x, g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ := by
  rw [integral_condExp hm]

/-! ### W2. A constant is known to every σ-algebra: R4, then R3 on `measurable_const`
`measurable_const : Measurable fun _ => c`; `integrable_const c : Integrable (fun _ => c) μ` for a
finite measure `μ`. -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (c : ℝ) : μ[(fun _ => c) | m] = fun _ => c := by
  apply condExp_of_stronglyMeasurable hm
  · exact measurable_const.stronglyMeasurable
  · exact integrable_const c

end E103Guide

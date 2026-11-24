/- Guide for E095 (Events and probability measures).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (an intersection `s ∩ t`, `2 * μ.real`).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory

namespace E095Guide

/-! # Part R · Reference entries -/

/-! ## Splitting a conjunction -/

/-! ### R1. `refine ⟨?_, ?_, ?_⟩` · goal → three goals
The term `⟨e₁, e₂, e₃⟩` (anonymous constructor) does the same and fills all three at once. -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : A ∧ B ∧ C := by
  refine ⟨?_, ?_, ?_⟩
  exacts [ha, hb, hc]

/-! ## Facts about `μ : Measure Ω` (values in `ENNReal`) -/

/-! ### R2. `prob_compl_eq_one_sub` · `MeasurableSet s → μ sᶜ = 1 - μ s` · goal
Used as a term, `prob_compl_eq_one_sub hs` is a proof of `μ sᶜ = 1 - μ s`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hs : MeasurableSet s) (P : ENNReal → Prop) (h : P (1 - μ s)) : P (μ sᶜ) := by
  rw [prob_compl_eq_one_sub hs]
  exact h

/-! ### R3. `measure_mono` · `s ⊆ t → μ s ≤ μ t` · goal `μ s ≤ μ t` → `s ⊆ t`
Any measure, probability or not. As a term: `measure_mono hst`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (hst : s ⊆ t) :
    μ s ≤ μ t := by
  apply measure_mono
  exact hst

/-! ### R4. `prob_le_one` · `μ s ≤ 1` for a probability measure · closes the goal
All its arguments are implicit or instances: write it with no arguments. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) :
    μ s ≤ 1 := by
  exact prob_le_one

/-! ## Facts about `μ.real` (values in `ℝ`) -/

/-! ### R5. `probReal_compl_eq_one_sub` · `MeasurableSet s → μ.real sᶜ = 1 - μ.real s` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hs : MeasurableSet s) (P : ℝ → Prop) (h : P (1 - μ.real s)) : P (μ.real sᶜ) := by
  rw [probReal_compl_eq_one_sub hs]
  exact h

/-! ### R6. `ring` · closes an identity of commutative rings such as `ℝ`; `μ.real s` is an unknown
It does not work in `ENNReal`, which is not a ring (no negatives; `-` is truncated). -/
example (a b : ℝ) : a + (b - a) = b := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Three facts about `s ∩ t`: R1, then R2, R3, R4 as terms
`hs.inter ht : MeasurableSet (s ∩ t)` (lemma `MeasurableSet.inter`) and
`Set.inter_subset_left : s ∩ t ⊆ s` supply the arguments. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s ∩ t)ᶜ = 1 - μ (s ∩ t) ∧ μ (s ∩ t) ≤ μ s ∧ μ s ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  exact prob_compl_eq_one_sub (hs.inter ht)
  exact measure_mono Set.inter_subset_left
  exact prob_le_one

/-! ### W2. A real-valued complement identity: R5, then R6 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hs : MeasurableSet s) : 2 * μ.real sᶜ = 2 - 2 * μ.real s := by
  rw [probReal_compl_eq_one_sub hs]
  ring

end E095Guide

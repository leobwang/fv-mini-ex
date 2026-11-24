/- Guide for M084 (Markov's inequality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (an upper bound by an indicator).
Assumed: Lean basics.
-/
import Mathlib

open ProbabilityTheory MeasureTheory

namespace M084Guide

/-! # Part R · Reference entries -/

/-! ## Naming the event -/

/-! ### R1. `set S := e` · context gains `S : T := e`; goal: every `e` → `S`
`S` is a local definition: Lean still knows `S` unfolds to `e` (definitional equality). -/
example {Ω : Type} (p : Ω → Prop) (P : Set Ω → Prop) (h : ∀ T : Set Ω, P T) : P {ω | p ω} := by
  set S := {ω | p ω}
  exact h S

/-! ## Measurability of the event -/

/-! ### R2. `measurableSet_le` · `Measurable f → Measurable g → MeasurableSet {ω | f ω ≤ g ω}`
`apply` it: goal list → the two measurability goals. -/
example {Ω : Type} [MeasurableSpace Ω] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {ω | f ω ≤ g ω} := by
  apply measurableSet_le
  exacts [hf, hg]

/-! ### R3. `measurable_const` · closes `Measurable fun x => c` -/
example {Ω : Type} [MeasurableSpace Ω] (c : ℝ) : Measurable (fun _ : Ω => c) := by
  exact measurable_const

/-! ## The pointwise comparison -/

/-! ### R4. `intro ω` on `f ≤ g` · context gains `ω`; goal → `f ω ≤ g ω`
On functions, `f ≤ g` is by definition `∀ ω, f ω ≤ g ω` (lemma `Pi.le_def`). -/
example {Ω : Type} (f g : Ω → ℝ) (h : ∀ ω, f ω ≤ g ω) : f ≤ g := by
  intro ω
  exact h ω

/-! ### R5. `by_cases h : ω ∈ S` · goal list: one goal → two, with `h : ω ∈ S` / `h : ω ∉ S` -/
example {Ω : Type} (S : Set Ω) (ω : Ω) (Q : Prop) (h1 : ω ∈ S → Q) (h2 : ω ∉ S → Q) : Q := by
  by_cases h : ω ∈ S
  exacts [h1 h, h2 h]

/-! ### R6. `Set.indicator_of_mem` · `ω ∈ S → S.indicator f ω = f ω` · goal -/
example {Ω M : Type} [Zero M] (S : Set Ω) (c : M) (ω : Ω) (hω : ω ∈ S) (P : M → Prop)
    (h : P c) : P (S.indicator (fun _ => c) ω) := by
  rw [Set.indicator_of_mem hω]
  exact h

/-! ### R7. `exact hω` with `hω : ω ∈ {x | p x}` · closes `p ω`
Membership in `{x | p x}` is by definition `p ω` (lemma `Set.mem_setOf_eq`); `exact` sees through
it, and through a `set` name as well. -/
example {Ω : Type} (p : Ω → Prop) (ω : Ω) (hω : ω ∈ {x | p x}) : p ω := by
  exact hω

/-! ### R8. `Set.indicator_of_notMem` · `ω ∉ S → S.indicator f ω = 0` · goal -/
example {Ω M : Type} [Zero M] (S : Set Ω) (f : Ω → M) (ω : Ω) (hω : ω ∉ S) (P : M → Prop)
    (h : P 0) : P (S.indicator f ω) := by
  rw [Set.indicator_of_notMem hω]
  exact h

/-! ## Integrability -/

/-! ### R9. `integrable_const c` · closes `Integrable (fun x => c) μ`; needs `[IsFiniteMeasure μ]` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (c : ℝ) :
    Integrable (fun _ : Ω => c) μ := by
  exact integrable_const c

/-! ### R10. `Integrable.indicator` · `Integrable f μ → MeasurableSet S → Integrable (S.indicator f) μ`
`apply` it: goal list → the two hypotheses. As a term: `hf.indicator hS`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (S : Set Ω)
    (hf : Integrable f μ) (hS : MeasurableSet S) : Integrable (S.indicator f) μ := by
  apply Integrable.indicator
  exacts [hf, hS]

/-! ## Integrating the comparison -/

/-! ### R11. `integral_mono` · `Integrable f μ → Integrable g μ → f ≤ g → ∫ f ∂μ ≤ ∫ g ∂μ`
`have := integral_mono hf hg hfg` · context gains `this`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : f ≤ g) (G : Prop) (k : (∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ) → G) : G := by
  have := integral_mono hf hg hfg
  exact k this

/-! ### R12. `integral_indicator_const` · `MeasurableSet S → ∫ x, S.indicator (fun _ => e) x ∂μ = μ.real S • e`
Explicit arguments: the constant `e`, then the measurability proof. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (hS : MeasurableSet S) (e : ℝ)
    (P : ℝ → Prop) (h : P (μ.real S • e)) : P (∫ ω, S.indicator (fun _ => e) ω ∂μ) := by
  rw [integral_indicator_const e hS]
  exact h

/-! ## Tidying the scalar -/

/-! ### R13. `smul_eq_mul` · `a • b = a * b` · goal -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R14. `mul_comm` · `a * b = b * a` · goal: the first product found is swapped -/
example {α : Type} [CommMagma α] (a b : α) (P : α → Prop) (h : P (b * a)) : P (a * b) := by
  rw [mul_comm]
  exact h

/-! ### R15. `rw [e] at hq` · context: `hq` rewritten; goal unchanged
`rwa [e] at hq` is `rw [e] at hq` followed by `assumption` (close the goal with a hypothesis). -/
example {α : Type} (a b : α) (Q : α → Prop) (hab : a = b) (hq : Q a) : Q b := by
  rw [hab] at hq
  exact hq

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A pointwise UPPER bound by an indicator: R1, R4, R5, then R6 / R8 in each case
Off `T`, `h : ω ∉ T` is by definition `¬ 0 < Y ω`; `not_lt.mp` turns it into `Y ω ≤ 0`. -/
example {Ω : Type} (Y : Ω → ℝ) (hY : ∀ ω, Y ω ≤ 1) :
    Y ≤ {ω | 0 < Y ω}.indicator (fun _ => 1) := by
  set T := {ω | 0 < Y ω}
  intro ω
  by_cases h : ω ∈ T
  · rw [Set.indicator_of_mem h]
    exact hY ω
  · rw [Set.indicator_of_notMem h]
    exact not_lt.mp h

/-! ### W2. Integrate it: R9, R10, R11, then R12, R13 and `mul_one` inside R15 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (S : Set Ω) (hS : MeasurableSet S) (hY : Integrable Y μ)
    (hYS : Y ≤ S.indicator (fun _ => 1)) : μ[Y] ≤ μ.real S := by
  have := integral_mono hY ((integrable_const 1).indicator hS) hYS
  rw [integral_indicator_const 1 hS] at this
  rwa [smul_eq_mul, mul_one] at this

/-! ### W3. R2 and R3 as one term, the constant on the right this time -/
example {Ω : Type} [MeasurableSpace Ω] (Y : Ω → ℝ) (hY : Measurable Y) :
    MeasurableSet {ω | Y ω ≤ 2} := by
  exact measurableSet_le hY measurable_const

end M084Guide

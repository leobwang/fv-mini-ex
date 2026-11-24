/- Guide for E099 (Independent random variables).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a zero covariance, a mean-zero factor).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace E099Guide

/-! # Part R · Reference entries -/

/-! ## Side conditions: measurability -/

/-! ### R1. `Measurable.aestronglyMeasurable` · `Measurable f → AEStronglyMeasurable f μ` · goal
`apply` turns the goal into `Measurable f`. As a term (dot notation): `hf.aestronglyMeasurable`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) :
    AEStronglyMeasurable f μ := by
  apply Measurable.aestronglyMeasurable
  exact hf

/-! ## Expectation of a product -/

/-! ### R2. `IndepFun.integral_mul_eq_mul_integral` · `X ⟂ᵢ[μ] Y → … → μ[X * Y] = μ[X] * μ[Y]` · goal
Arguments: the independence proof, then `AEStronglyMeasurable X μ`, `AEStronglyMeasurable Y μ`.
Dot notation: `hXY.integral_mul_eq_mul_integral hX hY` for `hXY : X ⟂ᵢ[μ] Y`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (P : ℝ → Prop)
    (h : P (μ[X] * μ[Y])) : P μ[X * Y] := by
  rw [hXY.integral_mul_eq_mul_integral hX hY]
  exact h

/-! ### R3. `rw [hX]` with `hX : μ[X] = a` · goal: a known mean → its value
The goal prints `μ[X]` as `∫ (x : Ω), X x ∂μ`; it is the same term, so `rw` finds it. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (a : ℝ) (hX : μ[X] = a)
    (P : ℝ → Prop) (h : P a) : P μ[X] := by
  rw [hX]
  exact h

/-! ### R4. `norm_num` · closes an equation between real numerals -/
example : (4 : ℝ) * 5 = 20 := by norm_num

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Independent variables have zero covariance: R1 (twice), R2, then `ring`
The expression `μ[U * V] - μ[U] * μ[V]` is `Cov[U, V]`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (U V : Ω → ℝ) (hU : Measurable U)
    (hV : Measurable V) (hUV : U ⟂ᵢ[μ] V) : μ[U * V] - μ[U] * μ[V] = 0 := by
  rw [hUV.integral_mul_eq_mul_integral hU.aestronglyMeasurable hV.aestronglyMeasurable]
  ring

/-! ### W2. A mean-zero factor kills the product's mean: R1, R2, R3, R4 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (U V : Ω → ℝ) (hU : Measurable U)
    (hV : Measurable V) (hUV : U ⟂ᵢ[μ] V) (h0 : μ[U] = 0) : μ[U * V] = 0 := by
  rw [hUV.integral_mul_eq_mul_integral hU.aestronglyMeasurable hV.aestronglyMeasurable]
  rw [h0]
  norm_num

end E099Guide

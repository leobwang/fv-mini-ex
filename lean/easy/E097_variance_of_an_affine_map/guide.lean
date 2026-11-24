/- Guide for E097 (Variance of an affine map).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g`) in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (two scalings, a side goal).
Assumed: Lean basics. The probability setup (`MeasurableSpace`, `Measure`, `IsProbabilityMeasure`) is
explained in cheatsheet.md, "Reading the goals".
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace E097Guide

/-! # Part R · Reference entries -/

/-! ## Measurability of a scaled random variable -/

/-! ### R1. `AEStronglyMeasurable.const_mul` · context gains `AEStronglyMeasurable (fun x => c * f x) μ`
`AEStronglyMeasurable f μ → ∀ c, AEStronglyMeasurable (fun x => c * f x) μ`. With `hf` in the context,
dot notation `hf.const_mul c` is this lemma applied to `hf` and `c`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (c : ℝ) (G : Prop) (g : AEStronglyMeasurable (fun ω => c * f ω) μ → G) : G := by
  have hg := hf.const_mul c
  exact g hg

/-! ## Rewriting a variance -/

/-! ### R2. `variance_add_const` · goal: `Var[fun ω => Y ω + c; μ]` → `Var[Y; μ]`
`AEStronglyMeasurable Y μ → ∀ c, Var[fun ω => Y ω + c; μ] = Var[Y; μ]`, for a probability measure `μ`.
The measurability proof fixes `Y`, so it decides which `Var[…]` the `rw` looks for. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (c : ℝ) (P : ℝ → Prop) (h : P Var[Y; μ]) :
    P Var[fun ω => Y ω + c; μ] := by
  rw [variance_add_const hY]
  exact h

/-! ### R3. `variance_const_mul` · goal: `Var[fun ω => c * Y ω; μ]` → `c ^ 2 * Var[Y; μ]`
`∀ c Y μ, Var[fun ω => c * Y ω; μ] = c ^ 2 * Var[Y; μ]`, for every measure, with no hypotheses. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (c : ℝ) (P : ℝ → Prop)
    (h : P (c ^ 2 * Var[Y; μ])) : P Var[fun ω => c * Y ω; μ] := by
  rw [variance_const_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Two scalings: R3 twice, then `ring` (`(c * d) ^ 2 = c ^ 2 * d ^ 2`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (c d : ℝ) :
    Var[fun ω => c * (d * Y ω); μ] = (c * d) ^ 2 * Var[Y; μ] := by
  rw [variance_const_mul]
  rw [variance_const_mul]
  ring

/-! ### W2. Two scalings and a shift: R1 twice builds the measurability, then R2, R3, R3, `ring` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (c d e : ℝ) :
    Var[fun ω => c * (d * Y ω) + e; μ] = (c * d) ^ 2 * Var[Y; μ] := by
  have h1 := (hY.const_mul d).const_mul c
  rw [variance_add_const h1]
  rw [variance_const_mul, variance_const_mul]
  ring

/-! ### W3. R2 with no argument: Lean finds `Y` from the goal and adds the measurability as a side goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (c d : ℝ) :
    Var[fun ω => Y ω + c; μ] + Var[fun ω => d * Y ω; μ] = (1 + d ^ 2) * Var[Y; μ] := by
  rw [variance_add_const]
  rw [variance_const_mul]
  ring
  exact hY

end E097Guide

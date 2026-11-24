/- Guide for M088 (Variance of a 0/1 variable).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on an object that is NOT the exercise's (a ±1-valued variable).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M088Guide

/-! # Part R · Reference entries -/

/-! ## An almost-everywhere bound from a pointwise one -/

/-! ### R1. `apply Filter.Eventually.of_forall` · goal `∀ᵐ x ∂μ, p x` → `∀ x, p x`
`Filter.Eventually.of_forall : (∀ x, p x) → ∀ᶠ x in F, p x`, and `∀ᵐ x ∂μ, p x` is `∀ᶠ x in ae μ, p x`.
What holds everywhere holds almost everywhere. Term form: `Filter.Eventually.of_forall (fun x => …)`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop) (hp : ∀ x, p x) :
    ∀ᵐ x ∂μ, p x := by
  apply Filter.Eventually.of_forall
  exact hp

/-! ### R2. `rcases hpq x with h | h` · goal list: one goal per side of `p x ∨ q x`
`hpq : ∀ x, p x ∨ q x` is first applied to the point `x`, then split. -/
example {Ω : Type} (p q : Ω → Prop) (hpq : ∀ x, p x ∨ q x) (x : Ω) (G : Prop)
    (hp : p x → G) (hq : q x → G) : G := by
  rcases hpq x with h | h
  exacts [hp h, hq h]

/-! ### R3. `Set.mem_Icc` · goal `t ∈ Set.Icc a b` → `a ≤ t ∧ t ≤ b`
`Set.Icc a b` is the closed interval `[a, b]`. `simp` uses this lemma by itself. -/
example {α : Type} [Preorder α] (a b t : α) (P : Prop → Prop) (h : P (a ≤ t ∧ t ≤ b)) :
    P (t ∈ Set.Icc a b) := by
  rw [Set.mem_Icc]
  exact h

/-! ### R4. `simp [h]` with `h : t = c` (a numeral) · closes `t ∈ Set.Icc a b` for numerals `a ≤ c ≤ b`
`simp` rewrites `t` to `c` with `h`, applies R3, and decides `a ≤ c ∧ c ≤ b`. -/
example (t : ℝ) (h : t = 2) : t ∈ Set.Icc (0 : ℝ) 2 := by
  simp [h]

/-! ## From the bound to `MemLp` -/

/-! ### R5. `Measurable.aestronglyMeasurable` · context gains `AEStronglyMeasurable f μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hm : Measurable f) (G : Prop)
    (k : AEStronglyMeasurable f μ → G) : G := by
  have hs : AEStronglyMeasurable f μ := hm.aestronglyMeasurable
  exact k hs

/-! ### R6. `memLp_of_bounded` · context gains `MemLp f 2 μ`
`memLp_of_bounded : (∀ᵐ x ∂μ, f x ∈ Set.Icc a b) → AEStronglyMeasurable f μ → ∀ p, MemLp f p μ`
on a finite measure: a bounded measurable function lies in every `Lᵖ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (a b : ℝ)
    (hb : ∀ᵐ x ∂μ, f x ∈ Set.Icc a b) (hs : AEStronglyMeasurable f μ) (G : Prop)
    (k : MemLp f 2 μ → G) : G := by
  have hL : MemLp f 2 μ := memLp_of_bounded hb hs 2
  exact k hL

/-! ## A function equation -/

/-! ### R7. `funext x` · goal `f ^ 2 = g` (functions) → `(f ^ 2) x = g x` at a fresh point `x` -/
example {Ω : Type} (f g : Ω → ℝ) (h : ∀ x, (f ^ 2) x = g x) : f ^ 2 = g := by
  funext x
  exact h x

/-! ### R8. `Pi.pow_apply` · goal `(f ^ n) x` → `f x ^ n` (`simp` uses it by itself) -/
example {Ω : Type} (f : Ω → ℝ) (x : Ω) (P : ℝ → Prop) (h : P (f x ^ 2)) : P ((f ^ 2) x) := by
  rw [Pi.pow_apply]
  exact h

/-! ## The variance -/

/-! ### R9. `variance_eq_sub` · goal `Var[f; μ]` → `E[f²] - (E f)²`
`variance_eq_sub : MemLp f 2 μ → Var[f; μ] = ∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2`
(probability measure). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (P : ℝ → Prop) (h : P (∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2)) :
    P (Var[f; μ]) := by
  rw [variance_eq_sub hf]
  exact h

/-! ### R10. `rw [e]` with `e : f ^ 2 = g` · goal: `f ^ 2` replaced, even under `∫ x, …`
The pattern `f ^ 2` does not mention the bound `x`, so `rw` can reach it inside the integral. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (e : f ^ 2 = g) (P : ℝ → Prop)
    (h : P (∫ x, g x ∂μ)) : P (∫ x, (f ^ 2) x ∂μ) := by
  rw [e]
  exact h

/-! ### R11. `ring` · closes a commutative-ring identity; each `∫ …` counts as one unknown -/
example (u v : ℝ) : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A ±1-valued measurable `g` is in `L²`: R1, intro, R2, R4, then R6 with R5 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hg : Measurable g) (hpm : ∀ ω, g ω = -1 ∨ g ω = 1) : MemLp g 2 μ := by
  have hb : ∀ᵐ ω ∂μ, g ω ∈ Set.Icc (-1 : ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    rcases hpm ω with h | h <;> simp [h]
  exact memLp_of_bounded hb hg.aestronglyMeasurable 2

/-! ### W2. Its square is the constant function `1`: R7, R2, `simp [h]` (R8 inside) -/
example {Ω : Type} (g : Ω → ℝ) (hpm : ∀ ω, g ω = -1 ∨ g ω = 1) : g ^ 2 = 1 := by
  funext ω
  rcases hpm ω with h | h
  all_goals simp [h]

/-! ### W3. So `Var g = 1 - (E g)²`: R9, R10, then `simp` evaluates `∫ 1 = 1` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hL2 : MemLp g 2 μ) (hsq : g ^ 2 = 1) : Var[g; μ] = 1 - (∫ ω, g ω ∂μ) ^ 2 := by
  rw [variance_eq_sub hL2]
  rw [hsq]
  simp

end M088Guide

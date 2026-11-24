/- Guide for M099 (Central limit theorem for coin flips).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`Q` stands for "the rest of your goal": the step changes only the part shown inside `Q (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (±1-valued sign variables).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace M099Guide

/-! # Part R · Reference entries -/

/-! ## A pointwise fact → an almost-everywhere fact -/

/-! ### R1. `Filter.Eventually.of_forall` · goal `∀ᵐ x ∂μ, Q x` → `∀ x, Q x`
What holds for every `x` holds for `μ`-almost every `x`. As a term: `Filter.Eventually.of_forall fun x => …`. -/
example {α : Type} [MeasurableSpace α] (μ : Measure α) (Q : α → Prop) (h : ∀ x, Q x) :
    ∀ᵐ x ∂μ, Q x := by
  apply Filter.Eventually.of_forall
  exact h

/-! ### R2. `rcases h with h | h` · `h : A ∨ B` → goal list: one goal with `h : A`, one with `h : B` -/
example {α : Type} (x a b : α) (Q : α → Prop) (h : x = a ∨ x = b) (ha : Q a) (hb : Q b) : Q x := by
  rcases h with h | h
  · rw [h]; exact ha
  · rw [h]; exact hb

/-! ### R3. `Set.mem_Icc` · `x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b` · goal: membership → two inequalities
`simp` applies it by itself: `simp [h]` with `h : x = 0` closes `x ∈ Set.Icc 0 1`. -/
example (x a b : ℝ) (h : a ≤ x ∧ x ≤ b) : x ∈ Set.Icc a b := by
  rw [Set.mem_Icc]
  exact h

/-! ## Square-integrability -/

/-! ### R4. `memLp_of_bounded` · goal `MemLp f p μ` → goal list: an a.e. bound and measurability
`memLp_of_bounded hb hm p : MemLp f p μ` for a finite measure `μ`. Here the bounds `a b` are given by
name, so the goals contain no unknowns. -/
example {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (a b : ℝ)
    (hb : ∀ᵐ x ∂μ, f x ∈ Set.Icc a b) (hm : AEStronglyMeasurable f μ) : MemLp f 2 μ := by
  refine memLp_of_bounded (a := a) (b := b) ?_ ?_ 2
  exacts [hb, hm]

/-! ### R5. `Measurable.aestronglyMeasurable` · goal `AEStronglyMeasurable f μ` → `Measurable f`
With `hm : Measurable f` write the term `hm.aestronglyMeasurable` (dot notation). -/
example {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (hm : Measurable f) :
    AEStronglyMeasurable f μ := by
  apply Measurable.aestronglyMeasurable
  exact hm

/-! ## Equations between functions -/

/-! ### R6. `funext x` · goal `f = g` (functions) → context gains `x`, goal `f x = g x` -/
example {α : Type} (f g : α → ℝ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-! ### R7. `Pi.pow_apply` · `(f ^ n) x = f x ^ n` · goal: power of a function, evaluated -/
example {α : Type} (f : α → ℝ) (n : ℕ) (x : α) (Q : ℝ → Prop) (h : Q (f x ^ n)) : Q ((f ^ n) x) := by
  rw [Pi.pow_apply]
  exact h

/-! ## Variance -/

/-! ### R8. `variance_eq_sub` · `MemLp ξ 2 μ → Var[ξ; μ] = μ[ξ ^ 2] - μ[ξ] ^ 2` · goal
Needs a probability measure. `μ[g]` is notation for `∫ x, g x ∂μ`, and Lean prints the integral. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → ℝ)
    (hξ : MemLp ξ 2 μ) (Q : ℝ → Prop) (h : Q (μ[ξ ^ 2] - μ[ξ] ^ 2)) : Q Var[ξ; μ] := by
  rw [variance_eq_sub hξ]
  exact h

/-! ## Fitting a hypothesis, the CLT, closing -/

/-! ### R9. `rwa [h]` · goal rewritten with `h`, then closed by a hypothesis (`rw [h]; assumption`)
Here it turns a variance written one way into the form a hypothesis about a Gaussian law has. -/
example {Ω' : Type} [MeasurableSpace Ω'] (μ' : Measure Ω') (Z : Ω' → ℝ) (v w : ℝ) (h : v = w)
    (hZ : HasLaw Z (gaussianReal 0 w.toNNReal) μ') : HasLaw Z (gaussianReal 0 v.toNNReal) μ' := by
  rwa [h]

/-! ### R10. `tendstoInDistribution_inv_sqrt_mul_sum_sub` (the CLT) · goal → four obligations
For i.i.d. square-integrable `ξ k`, `(√n)⁻¹ * (ξ 0 + … + ξ (n-1) - n * μ[ξ 0])` tends in distribution
to any `Z` with law `N(0, Var[ξ 0; μ])`. Usually applied as a term to its four arguments. -/
example {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (ξ : ℕ → Ω → ℝ)
    (Z : Ω' → ℝ) (hZ : HasLaw Z (gaussianReal 0 Var[ξ 0; μ].toNNReal) μ') (h2 : MemLp (ξ 0) 2 μ)
    (hind : iIndepFun ξ μ) (hid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * (∑ k ∈ Finset.range n, ξ k ω - n * μ[ξ 0]))
      Filter.atTop Z (fun _ => μ) μ' := by
  refine tendstoInDistribution_inv_sqrt_mul_sum_sub ?_ ?_ ?_ ?_
  exacts [hZ, h2, hind, hid]

/-! ### R11. `simpa [h] using t` · closes the goal: simplifies both `t` and the goal with `h`, then matches -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (ξ : Ω → ℝ) (m : ℝ) (hm : μ[ξ] = m)
    (Q : ℝ → Prop) (t : Q μ[ξ]) : Q m := by
  simpa [hm] using t

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A ±1-valued `f` is a.e. in `[-1, 1]`: R1 as a term, R2, then `simp [h]` (R3) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : ∀ ω, f ω = -1 ∨ f ω = 1) :
    ∀ᵐ ω ∂μ, f ω ∈ Set.Icc (-1 : ℝ) 1 := Filter.Eventually.of_forall fun ω => by
  rcases hf ω with h | h <;> simp [h]

/-! ### W2. Its variance from its mean: R4 with R5, R6 with R7 (inside `simp`), R8 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : ∀ ω, f ω = -1 ∨ f ω = 1) (hm : Measurable f) (m : ℝ) (hm0 : μ[f] = m) :
    Var[f; μ] = 1 - m ^ 2 := by
  have hb : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc (-1 : ℝ) 1 := Filter.Eventually.of_forall fun ω => by
    rcases hf ω with h | h <;> simp [h]
  have hL2 : MemLp f 2 μ := memLp_of_bounded hb hm.aestronglyMeasurable 2
  have hsq : f ^ 2 = 1 := by
    funext ω
    rcases hf ω with h | h <;> simp [h]
  rw [variance_eq_sub hL2, hsq, hm0]
  simp

/-! ### W3. CLT for mean-zero, variance-one signs: R10 as a term, then R11 removes `n * 0` -/
example {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (ξ : ℕ → Ω → ℝ)
    (Z : Ω' → ℝ) (h2 : MemLp (ξ 0) 2 μ) (hind : iIndepFun ξ μ)
    (hid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) (hm0 : μ[ξ 0] = 0) (hv : Var[ξ 0; μ] = 1)
    (hZ : HasLaw Z (gaussianReal 0 1) μ') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ξ k ω)
      Filter.atTop Z (fun _ => μ) μ' := by
  have hZ' : HasLaw Z (gaussianReal 0 Var[ξ 0; μ].toNNReal) μ' := by
    simpa [hv] using hZ
  have := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ' h2 hind hid
  simpa [hm0] using this

end M099Guide

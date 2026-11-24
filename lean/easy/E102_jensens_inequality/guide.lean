/- Guide for E102 (Jensen's inequality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the fourth power `x ^ 4`).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory

namespace E102Guide

/-! # Part R · Reference entries -/

/-! ## Jensen's inequality -/

/-! ### R1. `ConvexOn.map_integral_le` · goal list: `g (∫ f) ≤ ∫ g ∘ f` → five side goals
Give the convexity proof `hg` as the first argument; it fixes `g` and `s`. Each `?_` becomes a goal. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (g : ℝ → ℝ) (s : Set ℝ) (hg : ConvexOn ℝ s g) (hc : ContinuousOn g s) (hs : IsClosed s)
    (hae : ∀ᵐ x ∂μ, f x ∈ s) (hf : Integrable f μ) (hgf : Integrable (g ∘ f) μ) :
    g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  refine ConvexOn.map_integral_le hg ?_ ?_ ?_ ?_ ?_
  exacts [hc, hs, hae, hf, hgf]

/-! ## The convex function `Real.exp` -/

/-! ### R2. `convexOn_exp` · closes `ConvexOn ℝ Set.univ Real.exp` -/
example : ConvexOn ℝ Set.univ Real.exp := by
  exact convexOn_exp

/-! ### R3. `Continuous.continuousOn` · goal: `ContinuousOn g s` → `Continuous g`
As a term: `hc.continuousOn` turns `hc : Continuous g` into `ContinuousOn g s` for any `s`. -/
example {α β : Type} [TopologicalSpace α] [TopologicalSpace β] (g : α → β) (s : Set α)
    (h : Continuous g) : ContinuousOn g s := by
  apply Continuous.continuousOn
  exact h

/-! ### R4. `Real.continuous_exp` · closes `Continuous Real.exp` -/
example : Continuous Real.exp := by
  exact Real.continuous_exp

/-! ## The side conditions on `s = Set.univ` -/

/-! ### R5. `isClosed_univ` · closes `IsClosed Set.univ` -/
example {X : Type} [TopologicalSpace X] : IsClosed (Set.univ : Set X) := by
  exact isClosed_univ

/-! ### R6. `ae_of_all` · goal: `∀ᵐ x ∂μ, p x` → `∀ a, p a` (true everywhere ⇒ almost everywhere) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop) (h : ∀ x, p x) :
    ∀ᵐ x ∂μ, p x := by
  apply ae_of_all
  exact h

/-! ### R7. `Set.mem_univ` · closes `b ∈ Set.univ`
After R6 the goal is `∀ a, f a ∈ Set.univ`; the term `fun _ => Set.mem_univ _` proves it. -/
example {β : Type} (b : β) : b ∈ Set.univ := by
  exact Set.mem_univ b

/-! ### R8. `Function.comp_def` · goal: `g ∘ f` → `fun x => g (f x)`
The two are equal by definition, so `exact h` with `h` about `fun x => g (f x)` closes a goal about
`g ∘ f` without this rewrite. -/
example {α β γ : Type} (f : α → β) (g : β → γ) (P : (α → γ) → Prop) (h : P (fun x => g (f x))) :
    P (g ∘ f) := by
  rw [Function.comp_def]
  exact h

/-! ## The convex function `x ↦ x ^ n` -/

/-! ### R9. `Even.convexOn_pow` · goal: `ConvexOn ℝ Set.univ fun x => x ^ n` → `Even n` -/
example (n : ℕ) (hn : Even n) : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ n) := by
  apply Even.convexOn_pow
  exact hn

/-! ### R10. `even_two` · closes `Even 2` -/
example : Even (2 : ℕ) := by
  exact even_two

/-! ### R11. `continuous_pow` · closes `Continuous fun x => x ^ n` -/
example (n : ℕ) : Continuous fun (x : ℝ) => x ^ n := by
  exact continuous_pow n

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Jensen for the fourth power, in tactic mode: R1 with R9, then R3 + R11, R5, R6 + R7
`(by decide : Even 4)` proves `Even 4` by computation; the ascription `: Even 4` fixes `n = 4`.
The last goal `Integrable ((fun x => x ^ 4) ∘ Y) ν` is closed by `h4`, stated with
`fun ω => Y ω ^ 4` (R8). -/
example {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (Y : Ω → ℝ)
    (hY : Integrable Y ν) (h4 : Integrable (fun ω => Y ω ^ 4) ν) :
    (∫ ω, Y ω ∂ν) ^ 4 ≤ ∫ ω, Y ω ^ 4 ∂ν := by
  refine ConvexOn.map_integral_le (Even.convexOn_pow (by decide : Even 4)) ?_ ?_ ?_ ?_ ?_
  · exact (continuous_pow 4).continuousOn
  · exact isClosed_univ
  · exact ae_of_all _ fun _ => Set.mem_univ _
  · exact hY
  · exact h4

/-! ### W2. The same inequality as one term: every `?_` of W1 filled in place -/
example {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (Y : Ω → ℝ)
    (hY : Integrable Y ν) (h4 : Integrable (fun ω => Y ω ^ 4) ν) :
    (∫ ω, Y ω ∂ν) ^ 4 ≤ ∫ ω, Y ω ^ 4 ∂ν :=
  ConvexOn.map_integral_le (Even.convexOn_pow (by decide : Even 4)) (continuous_pow 4).continuousOn
    isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hY h4

end E102Guide

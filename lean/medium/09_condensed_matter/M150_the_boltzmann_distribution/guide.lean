/- Guide for M150 (The Boltzmann distribution).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (plain weight functions `g : ι → ℝ`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M150Guide

/-! # Part R · Reference entries -/

/-! ## The partition function is positive -/

/-! ### R1. `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos β` · context gains `hZ : 0 < Z(β)`
`CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos [Nonempty ι] (β : ℝ) :
  0 < 𝓒.mathematicalPartitionFunctionBetaReal β`. The `[Nonempty ι]` bracket must be in context. -/
example {ι : Type} [MeasurableSpace ι] [Fintype ι] [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (β : ℝ)
    (G : Prop) (h : 0 < 𝓒.mathematicalPartitionFunctionBetaReal β → G) : G := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos β
  exact h hZ

/-! ## Splitting the goal -/

/-! ### R2. `refine ⟨fun i => ?_, ?_⟩` · goal `(∀ i, A i) ∧ B` → two goals; the first gains `i : ι` -/
example {ι : Type} (A : ι → Prop) (B : Prop) (ha : ∀ i, A i) (hb : B) : (∀ i, A i) ∧ B := by
  refine ⟨fun i => ?_, ?_⟩
  exacts [ha i, hb]

/-! ## Unfolding the probability -/

/-! ### R3. `unfold CanonicalEnsemble.probabilityBetaReal` · goal: `p_β(i)` → `exp (-β E i) / Z(β)`
`rexp` is how Lean prints `Real.exp`. `unfold` also works under `∑`. -/
example {ι : Type} [MeasurableSpace ι] [Fintype ι] (𝓒 : CanonicalEnsemble ι) (β : ℝ) (i : ι)
    (P : ℝ → Prop) (h : P (Real.exp (-β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal β)) :
    P (𝓒.probabilityBetaReal β i) := by
  unfold CanonicalEnsemble.probabilityBetaReal
  exact h

/-! ## Closing `0 < …` -/

/-! ### R4. `positivity` · closes `0 < e` for `e` built from `exp`, `/`, `*`, `+` and positive atoms
An atom such as `Z` counts as positive when a hypothesis `hZ : 0 < Z` is in the context. -/
example (x Z : ℝ) (hZ : 0 < Z) : 0 < Real.exp x / Z := by
  positivity

/-! ## The sum -/

/-! ### R5. `Finset.sum_div` · `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; `rw [← Finset.sum_div]` pulls
a common denominator out of a sum. `∑ i, f i` is `∑ i ∈ Finset.univ, f i`. -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) / a)) :
    P (∑ i, f i / a) := by
  rw [← Finset.sum_div]
  exact h

/-! ### R6. `unfold CanonicalEnsemble.mathematicalPartitionFunctionBetaReal` · goal: `Z(β)` → its sum
You rarely need to run it: `exact` and `div_self` (R8) see through this definition by themselves. -/
example {ι : Type} [MeasurableSpace ι] [Fintype ι] (𝓒 : CanonicalEnsemble ι) (β : ℝ)
    (P : ℝ → Prop) (h : P (∑ i, Real.exp (-β * 𝓒.energy i))) :
    P (𝓒.mathematicalPartitionFunctionBetaReal β) := by
  unfold CanonicalEnsemble.mathematicalPartitionFunctionBetaReal
  exact h

/-! ### R7. `hZ.ne'` (`LT.lt.ne'`) · from `hZ : 0 < a` get `a ≠ 0`; context gains it -/
example (a : ℝ) (G : Prop) (hZ : 0 < a) (h : a ≠ 0 → G) : G := by
  have hne := hZ.ne'
  exact h hne

/-! ### R8. `div_self` · `a ≠ 0 → a / a = 1` · closes the goal
`exact div_self h` accepts `x / y = 1` when `x` and `y` are equal after unfolding definitions. -/
example {α : Type} [DivisionRing α] (a : α) (h : a ≠ 0) : a / a = 1 := by
  exact div_self h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A normalised weight `w g i = g i / ∑ j, g j`: unfold and pull out the sum in one
`simp only` (R3 + R5), then close with R7 + R8 -/
noncomputable def w {ι : Type} [Fintype ι] (g : ι → ℝ) (i : ι) : ℝ := g i / ∑ j, g j

example {ι : Type} [Fintype ι] (g : ι → ℝ) (hS : 0 < ∑ j, g j) : ∑ i, w g i = 1 := by
  simp only [w, ← Finset.sum_div]
  exact div_self hS.ne'

/-! ### W2. `positivity` proves a sum of exponentials positive by itself (it uses `[Nonempty ι]`) -/
example {ι : Type} [Fintype ι] [Nonempty ι] (y : ι → ℝ) (i : ι) :
    0 < Real.exp (y i) / ∑ j, Real.exp (y j) := by
  positivity

end M150Guide

/- Guide for E120 (Heat capacity is non-negative).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on a quotient that is NOT the exercise's (any measure `μ`, any `f`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Constants

namespace E120Guide

/-! # Part R · Reference entries -/

/-! ## From the heat capacity to a quotient -/

/-! ### R1. `rw [fluctuation_dissipation_theorem_finite 𝓒 T hT]` · goal: `𝓒.heatCapacity T` → `Var / (kB * T²)`
The lemma: for a finite ensemble and `0 < T.val`,
`𝓒.heatCapacity T = 𝓒.energyVariance T / (kB * ↑T.val ^ 2)`. You pass the explicit arguments
`𝓒`, `T`, `hT`; Lean finds the `[…]` instance arguments in the context by itself. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [Nonempty ι] (𝓒 : CanonicalEnsemble ι)
    [MeasurableSingletonClass ι] [𝓒.IsFinite] (T : Temperature) (hT : 0 < T.val)
    (P : ℝ → Prop) (h : P (𝓒.energyVariance T / (kB * ↑T.val ^ 2))) :
    P (𝓒.heatCapacity T) := by
  rw [fluctuation_dissipation_theorem_finite 𝓒 T hT]
  exact h

/-! ### R2. `have hk := kB_pos` · context gains `hk : 0 < kB`; goal unchanged
`Constants.kB_pos : 0 < kB`. Without a type after `hk`, `have` takes the lemma's own statement. -/
example (G : Prop) (g : 0 < kB → G) : G := by
  have hk := kB_pos
  exact g hk

/-! ## A quotient of non-negatives -/

/-! ### R3. `apply div_nonneg` · goal `0 ≤ a / b` → two goals `0 ≤ a` (case `ha`) and `0 ≤ b` (case `hb`)
`div_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a / b`. Term form: `div_nonneg ha hb`. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  apply div_nonneg
  exact ha
  exact hb

/-! ## The numerator: an integral of a square -/

/-! ### R4. `unfold energyVariance` · goal: the name → its defining integral
`𝓒.energyVariance T` is defined as `∫ i, (𝓒.energy i - 𝓒.meanEnergy T) ^ 2 ∂𝓒.μProd T`. You need not
unfold it: `exact`/`apply` see through definitions. Unfold it to *see* that it is an integral. -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (P : ℝ → Prop)
    (h : P (∫ i, (𝓒.energy i - 𝓒.meanEnergy T) ^ 2 ∂𝓒.μProd T)) : P (𝓒.energyVariance T) := by
  unfold energyVariance
  exact h

/-! ### R5. `apply MeasureTheory.integral_nonneg` · goal `0 ≤ ∫ x, f x ∂μ` → `0 ≤ f`
`MeasureTheory.integral_nonneg : 0 ≤ f → 0 ≤ ∫ x, f x ∂μ`: a pointwise non-negative function has a
non-negative integral, for every measure `μ` (no integrability needed). -/
example {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (f : α → ℝ) (hf : 0 ≤ f) :
    0 ≤ ∫ x, f x ∂μ := by
  apply MeasureTheory.integral_nonneg
  exact hf

/-! ### R6. `intro x` on `0 ≤ f` for a function `f` · context gains `x`; goal `0 x ≤ f x`
On functions, `≤` is pointwise: `0 ≤ f` means `∀ x, 0 x ≤ f x`, and `0 x` (the zero function at
`x`) is `0` by definition. So `intro x` works, and so does the term `fun x => …`. -/
example {α : Type} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ f := by
  intro x
  exact hf x

/-! ### R7. `sq_nonneg` · `sq_nonneg a : 0 ≤ a ^ 2` · closes the goal
`exact` accepts it for `0 x ≤ (fun x => g x ^ 2) x` too: that unfolds to `0 ≤ g x ^ 2`. -/
example (a : ℝ) : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

/-! ## The denominator -/

/-! ### R8. `positivity` · closes `0 ≤ e` / `0 < e` for a product, power, … of positive pieces
It knows squares and casts `↑t` of an `ℝ≥0` are `≥ 0`, but a constant such as `kB` is positive only
if a hypothesis says so (`hc` here, `hk` from R2 in the exercise). -/
example (c : ℝ) (t : NNReal) (hc : 0 < c) : 0 ≤ c * ↑t ^ 2 := by
  positivity

/-! # Part W · Worked combinations (not the exercise's quotient) -/

/-! ### W1. A variance-like quotient, one step at a time: R3, R5, R6, R7, R8 -/
example {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (g : α → ℝ) (m c : ℝ)
    (t : NNReal) (hc : 0 < c) : 0 ≤ (∫ x, (g x - m) ^ 2 ∂μ) / (c * ↑t ^ 2) := by
  apply div_nonneg
  · apply MeasureTheory.integral_nonneg
    intro x
    exact sq_nonneg _
  · positivity

/-! ### W2. The same in one term: `div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity)` -/
example {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (g : α → ℝ) (m c : ℝ)
    (t : NNReal) (hc : 0 < c) : 0 ≤ (∫ x, (g x - m) ^ 2 ∂μ) / (c * ↑t ^ 2) :=
  div_nonneg (MeasureTheory.integral_nonneg fun _ => sq_nonneg _) (by positivity)

end E120Guide

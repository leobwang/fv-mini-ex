/- Guide for M153 (Shifting the energy zero).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`𝓔 : CanonicalEnsemble ι` is any physlib canonical ensemble with microstates `ι`.
Part W: worked combinations on objects that are NOT the exercise's (energies doubled, plain weights).
Assumed: Lean basics.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M153Guide

/-! # Part R · Reference entries -/

/-! ## The partition function and a modified ensemble -/

/-! ### R1. `simp only [mathematicalPartitionFunctionBetaReal]` · goal: `Z(b)` → its sum
`𝓔.mathematicalPartitionFunctionBetaReal b` is defined as `∑ i, Real.exp (-b * 𝓔.energy i)`. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)
    (P : ℝ → Prop) (h : P (∑ i, Real.exp (-b * 𝓔.energy i))) :
    P (𝓔.mathematicalPartitionFunctionBetaReal b) := by
  simp only [mathematicalPartitionFunctionBetaReal]
  exact h

/-! ### R2. `simp only [D]` for `D` built by structure update · goal: `(D 𝓔).energy i` → the new field
`{ 𝓔 with energy := f, energy_measurable := pf }` is `𝓔` with those two fields replaced; every other
field (`dof`, `μ`, …) is copied. `simp only [D]` unfolds `D` and reads off the field. -/
noncomputable def double {ι : Type} [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) :
    CanonicalEnsemble ι :=
  { 𝓔 with energy := fun i => 2 * 𝓔.energy i, energy_measurable := by fun_prop }

example {ι : Type} [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (i : ι) (P : ℝ → Prop)
    (h : P (2 * 𝓔.energy i)) : P ((double 𝓔).energy i) := by
  simp only [double]
  exact h

/-! ### R3. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal: constant into the sum
`∑ i, f i` is `∑ i ∈ Finset.univ, f i`, the sum over all of a finite type. -/
example {ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, a * f i)) :
    P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R4. `simp only [← Real.exp_add]` · `exp x * exp y` → `exp (x + y)`, also under `∑` · goal
The lemma is `Real.exp_add x y : rexp (x + y) = rexp x * rexp y`; `rexp` is how Lean prints `Real.exp`.
`rw [← Real.exp_add]` fails here: `rw` cannot rewrite a term that mentions the bound `i` of `∑ i, …`. -/
example {ι : Type} [Fintype ι] (u v : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, Real.exp (u i + v i))) :
    P (∑ i, Real.exp (u i) * Real.exp (v i)) := by
  simp only [← Real.exp_add]
  exact h

/-! ### R5. `congr 1` · goal `∑ i, f i = ∑ i, g i` → `f = g` (the summands, as functions) -/
example {ι : Type} [Fintype ι] (f g : ι → ℝ) (h : ∀ i, f i = g i) : ∑ i, f i = ∑ i, g i := by
  congr 1
  exact funext h

/-! ### R6. `funext i` · goal `f = g` (functions) → context gains `i`, goal `f i = g i` -/
example {ι : Type} (f g : ι → ℝ) (h : ∀ i, f i = g i) : f = g := by
  funext i
  exact h i

/-! ### R7. `ring_nf` · closes `rexp u = rexp v` when `u` and `v` are equal as ring expressions
`ring` fails here (it treats `rexp (…)` as an unknown and compares the unknowns literally);
`ring_nf` also normalises the arguments inside `rexp`, after which both sides are the same. -/
example (x y : ℝ) : Real.exp (x * (y + 1)) = Real.exp (x + x * y) := by
  ring_nf

/-! ## Boltzmann probabilities -/

/-! ### R8. `rw [probabilityBetaReal]` · goal: the FIRST ensemble's `p b i` → `exp (-b E i) / Z(b)`
`𝓔.probabilityBetaReal b i` is defined as `rexp (-b * 𝓔.energy i) / 𝓔.mathematicalPartitionFunctionBetaReal b`.
`rw` fixes the ensemble at the first match, so occurrences for another ensemble `𝓕` stay folded;
a second `rw [probabilityBetaReal]` unfolds those. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 𝓕 : CanonicalEnsemble ι) (b : ℝ) (i : ι)
    (P : ℝ → ℝ → Prop)
    (h : P (Real.exp (-b * 𝓔.energy i) / 𝓔.mathematicalPartitionFunctionBetaReal b)
      (𝓕.probabilityBetaReal b i)) :
    P (𝓔.probabilityBetaReal b i) (𝓕.probabilityBetaReal b i) := by
  rw [probabilityBetaReal]
  exact h

/-! ### R9. `have hE : (D 𝓔).energy i = … := rfl` · context gains the unfolded field
A field of a structure update is equal to the new value by definition, so `rfl` proves it. -/
example {ι : Type} [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (i : ι) (G : Prop)
    (g : (double 𝓔).energy i = 2 * 𝓔.energy i → G) : G := by
  have hE : (double 𝓔).energy i = 2 * 𝓔.energy i := rfl
  exact g hE

/-! ### R10. `rw [show u = v by ring]` · goal: rewrite with an equation proved on the spot -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (x * y + x)) : P (x * (y + 1)) := by
  rw [show x * (y + 1) = x * y + x by ring]
  exact h

/-! ### R11. `Real.exp_add` · `rexp (x + y) = rexp x * rexp y` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp x * Real.exp y)) : P (Real.exp (x + y)) := by
  rw [Real.exp_add]
  exact h

/-! ### R12. `mul_div_mul_left a b hc` · `hc : c ≠ 0 → c * a / (c * b) = a / b` · goal: cancel `c` -/
example {G₀ : Type} [CommGroupWithZero G₀] (a b c : G₀) (hc : c ≠ 0) (P : G₀ → Prop)
    (h : P (a / b)) : P (c * a / (c * b)) := by
  rw [mul_div_mul_left a b hc]
  exact h

/-! ### R13. `(Real.exp_pos x).ne'` · closes `rexp x ≠ 0`
`Real.exp_pos x : 0 < rexp x`; for `h : a < b`, `h.ne' : b ≠ a` (lemma `LT.lt.ne'`). -/
example (x : ℝ) : Real.exp x ≠ 0 := by
  exact (Real.exp_pos x).ne'

/-! ## Mean energy -/

/-! ### R14. `have hZ := 𝓔.mathematicalPartitionFunctionBetaReal_pos b` · context gains `0 < Z(b)`
Needs `[Nonempty ι]`: at least one microstate, so the sum of positive terms is positive. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [Nonempty ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)
    (G : Prop) (g : 0 < 𝓔.mathematicalPartitionFunctionBetaReal b → G) : G := by
  have hZ := 𝓔.mathematicalPartitionFunctionBetaReal_pos b
  exact g hZ

/-! ### R15. `simp only [probabilityBetaReal]` · goal: EVERY `p b i` → `exp (-b E i) / Z(b)`, also under `∑` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)
    (P : ℝ → Prop)
    (h : P (∑ i, Real.exp (-b * 𝓔.energy i) / 𝓔.mathematicalPartitionFunctionBetaReal b)) :
    P (∑ i, 𝓔.probabilityBetaReal b i) := by
  simp only [probabilityBetaReal]
  exact h

/-! ### R16. `Finset.sum_div` right to left · `∑ i ∈ s, f i / a` → `(∑ i ∈ s, f i) / a` · goal -/
example {ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) / a)) :
    P (∑ i, f i / a) := by
  rw [← Finset.sum_div]
  exact h

/-! ### R17. `div_self ha` · `ha : a ≠ 0 → a / a = 1` · closes the goal -/
example (a : ℝ) (ha : a ≠ 0) : a / a = 1 := by
  exact div_self ha

/-! ### R18. `simp only [meanEnergyBetaReal]` · goal: `U(b)` → `∑ i, E i * p b i` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)
    (P : ℝ → Prop) (h : P (∑ i, 𝓔.energy i * 𝓔.probabilityBetaReal b i)) :
    P (𝓔.meanEnergyBetaReal b) := by
  simp only [meanEnergyBetaReal]
  exact h

/-! ### R19. `simp only [hF]` with `hF : F = G` between functions · goal: every `F x` → `G x`, also under `∑` -/
example {ι : Type} [Fintype ι] (F G w : ι → ℝ) (hF : F = G) (P : ℝ → Prop)
    (h : P (∑ i, w i * G i)) : P (∑ i, w i * F i) := by
  simp only [hF]
  exact h

/-! ### R20. `simp only [add_mul]` · `(a + b) * c = a * c + b * c`, also under `∑` · goal
As in R4, `rw [add_mul]` fails when the product mentions the bound `i` of `∑ i, …`; `simp only` works. -/
example {ι : Type} [Fintype ι] (f g w : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, (f i * w i + g i * w i))) :
    P (∑ i, (f i + g i) * w i) := by
  simp only [add_mul]
  exact h

/-! ### R21. `Finset.sum_add_distrib` · `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i` · goal -/
example {ι : Type} [Fintype ι] (f g : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, f i + ∑ i, g i)) :
    P (∑ i, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R22. `Finset.mul_sum` right to left · `∑ i, a * f i` → `a * ∑ i, f i` · goal -/
example {ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ) (P : ℝ → Prop) (h : P (a * ∑ i, f i)) :
    P (∑ i, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R23. `mul_one` · `a * 1 = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Doubling every energy is the same as doubling `b`: R1, R2, R5, R6, R7 -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ) :
    (double 𝓔).mathematicalPartitionFunctionBetaReal b =
      𝓔.mathematicalPartitionFunctionBetaReal (2 * b) := by
  simp only [mathematicalPartitionFunctionBetaReal, double]
  congr 1
  funext i
  ring_nf

/-! ### W2. Normalised weights sum to one: R16, R17 -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (hpos : 0 < ∑ j, f j) :
    ∑ i, f i / ∑ j, f j = 1 := by
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

/-! ### W3. Cancelling an exponential factor: R11, R12, R13 -/
example (x y z : ℝ) : Real.exp (x + y) / (Real.exp x * z) = Real.exp y / z := by
  rw [Real.exp_add]
  rw [mul_div_mul_left _ _ (Real.exp_pos x).ne']

/-! ### W4. A weighted average of `f + c` with weights summing to one: R20, R21, R22, R23 -/
example {ι : Type} [Fintype ι] (f w : ι → ℝ) (c : ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, (f i + c) * w i = ∑ i, f i * w i + c := by
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hw, mul_one]

end M153Guide

/- Guide for M151 (Boltzmann factors).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is a goal the step leaves alone; `g` is only there to finish the example.
Part W: worked combinations on weights that are NOT the exercise's (no ensemble, other exponents).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M151Guide

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]

/-! # Part R · Reference entries -/

/-! ## Facts about the partition function -/

/-! ### R1. `mathematicalPartitionFunctionBetaReal_pos` · context gains `0 < Z(t)`
Needs `[Nonempty ι]`: a sum of positive terms over a nonempty finite set is positive. -/
example [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)
    (g : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t → G) : G := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos t
  exact g hZ

/-! ### R2. `LT.lt.ne'` (dot notation `hab.ne'`) · `a < b → b ≠ a`; context gains `b ≠ a`
From `hZ : 0 < Z` it gives `hZ.ne' : Z ≠ 0`, the form division lemmas ask for. -/
example {α : Type} [Preorder α] (a b : α) (hab : a < b) (G : Prop) (g : b ≠ a → G) : G := by
  have h := hab.ne'
  exact g h

/-! ### R3. `unfold probabilityBetaReal` · goal: the name `p` → its body `rexp (-t * E k) / Z(t)`
`simp only [probabilityBetaReal]` does the same here. -/
example (𝓒 : CanonicalEnsemble ι) (t : ℝ) (k : ι) (P : ℝ → Prop)
    (h : P (rexp (-t * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal t)) :
    P (𝓒.probabilityBetaReal t k) := by
  unfold probabilityBetaReal
  exact h

/-! ## The ratio: cancel `Z`, merge the exponentials -/

/-! ### R4. `div_div_div_cancel_right₀` · `c ≠ 0 → a / c / (b / c) = a / b` · goal -/
example {α : Type} [GroupWithZero α] (a b c : α) (hc : c ≠ 0) (P : α → Prop) (h : P (a / b)) :
    P (a / c / (b / c)) := by
  rw [div_div_div_cancel_right₀ hc]
  exact h

/-! ### R5. `Real.exp_sub` · `rexp (x - y) = rexp x / rexp y`; `rw [← Real.exp_sub]` merges a quotient -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (rexp (x - y))) : P (rexp x / rexp y) := by
  rw [← Real.exp_sub]
  exact h

/-! ### R6. `ring_nf` · closes `f A = f B` when `A` and `B` are equal as ring expressions
It normalises every ring subterm, even inside an unknown function `f`, then both sides agree. -/
example (f : ℝ → ℝ) (a x y : ℝ) : f (-a * x - -a * y) = f (-a * (x - y)) := by
  ring_nf

/-! ## The ordering: compare numerators, then exponents -/

/-! ### R7. `div_le_div_iff_of_pos_right` · `0 < c → (a / c ≤ b / c ↔ a ≤ b)` · goal -/
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_le_div_iff_of_pos_right hc]
  exact h

/-! ### R8. `Real.exp_le_exp` · `rexp x ≤ rexp y ↔ x ≤ y` · goal: compare exponents -/
example (x y : ℝ) (h : x ≤ y) : rexp x ≤ rexp y := by
  rw [Real.exp_le_exp]
  exact h

/-! ### R9. `nlinarith` · closes a (non)linear inequality using products of hypotheses
Here it multiplies `0 ≤ t` by `0 ≤ y - x`; `linarith` alone cannot, since `t * x` is not linear. -/
example (t x y : ℝ) (ht : 0 ≤ t) (hxy : x ≤ y) : -t * y ≤ -t * x := by
  nlinarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A ratio with a common positive denominator: R2 → R4 → R5 → R6 -/
example (c x y : ℝ) (hc : 0 < c) : rexp (2 * x) / c / (rexp (2 * y) / c) = rexp (2 * (x - y)) := by
  rw [div_div_div_cancel_right₀ hc.ne']
  rw [← Real.exp_sub]
  ring_nf

/-! ### W2. An ordering with a common positive denominator: R7 → R8 → R9 -/
example (c s x y : ℝ) (hc : 0 < c) (hs : 0 ≤ s) (hxy : x ≤ y) :
    rexp (-(3 * s) * y) / c ≤ rexp (-(3 * s) * x) / c := by
  rw [div_le_div_iff_of_pos_right hc]
  rw [Real.exp_le_exp]
  nlinarith

end M151Guide

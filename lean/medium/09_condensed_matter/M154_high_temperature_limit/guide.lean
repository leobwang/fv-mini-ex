/- Guide for M154 (High-temperature limit).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g`) in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other functions of `x : ℝ`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real Filter Topology

namespace M154Guide

/-! # Part R · Reference entries -/

/-! ## Unfolding the physlib definitions -/

/-! ### R1. `unfold CanonicalEnsemble.probabilityBetaReal` · goal: `𝓒.probabilityBetaReal b k` → its body
Definition: `𝓒.probabilityBetaReal b k = rexp (-b * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal b`.
`unfold` also works under `fun b => …`. -/
example {ι : Type} [MeasurableSpace ι] [Fintype ι] (𝓒 : CanonicalEnsemble ι) (k : ι)
    (P : (ℝ → ℝ) → Prop)
    (h : P fun b => rexp (-b * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal b) :
    P fun b => 𝓒.probabilityBetaReal b k := by
  unfold CanonicalEnsemble.probabilityBetaReal
  exact h

/-! ### R2. `unfold CanonicalEnsemble.mathematicalPartitionFunctionBetaReal` · goal: `Z(b)` → its sum
Definition: `𝓒.mathematicalPartitionFunctionBetaReal b = ∑ i, rexp (-b * 𝓒.energy i)`. -/
example {ι : Type} [MeasurableSpace ι] [Fintype ι] (𝓒 : CanonicalEnsemble ι)
    (P : (ℝ → ℝ) → Prop) (h : P fun b => ∑ i, rexp (-b * 𝓒.energy i)) :
    P fun b => 𝓒.mathematicalPartitionFunctionBetaReal b := by
  unfold CanonicalEnsemble.mathematicalPartitionFunctionBetaReal
  exact h

/-! ## Continuity of a quotient -/

/-! ### R3. `refine Continuous.div ?_ ?_ ?_` · goal list: `Continuous (f / g)` → three goals
`Continuous.div : Continuous f → Continuous g → (∀ x, g x ≠ 0) → Continuous (f / g)`, for
`f g : α → G₀` with `G₀` a field such as `ℝ` or `ℂ`. -/
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (h0 : ∀ x, g x ≠ 0) :
    Continuous fun x => f x / g x := by
  refine Continuous.div ?_ ?_ ?_
  exact hf
  exact hg
  exact h0

/-! ### R4. `fun_prop` · closes `Continuous fun b => …` built from `rexp`, `*`, `-`, `+`, `∑`, constants -/
example (c : ℝ) : Continuous fun b : ℝ => rexp (-b * c) := by
  fun_prop

example {ι : Type} [Fintype ι] (E : ι → ℝ) : Continuous fun b : ℝ => ∑ j, rexp (-b * E j) := by
  fun_prop

/-! ## The denominator is never zero -/

/-! ### R5. `CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos` · context gains `0 < Z(b)`
`[Nonempty ι] (b : ℝ) : 0 < 𝓒.mathematicalPartitionFunctionBetaReal b` (a sum of positive exponentials). -/
example {ι : Type} [MeasurableSpace ι] [Fintype ι] [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (b : ℝ)
    (Q : Prop) (g : 0 < 𝓒.mathematicalPartitionFunctionBetaReal b → Q) : Q := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
  exact g hZ

/-! ### R6. `LT.lt.ne'` · `h : a < b` gives `h.ne' : b ≠ a`; `exact h.ne'` closes the goal -/
example {α : Type} [Preorder α] (a b : α) (h : a < b) : b ≠ a := by
  exact h.ne'

/-! ## From continuity to a limit -/

/-! ### R7. `Continuous.tendsto` · context gains `Tendsto f (𝓝 x) (𝓝 (f x))`
`hf.tendsto x`: a continuous `f` tends to its own value `f x` as the input tends to `x`
(for any topological spaces, e.g. `ℝ → ℝ`, `ℝ → ℂ`). -/
example (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) (Q : Prop) (g : Tendsto f (𝓝 x) (𝓝 (f x)) → Q) : Q := by
  have ht := hf.tendsto x
  exact g ht

/-! ## Evaluating at `b = 0` (`simp` applies these by itself) -/

/-! ### R8. `neg_zero`, `zero_mul`, `Real.exp_zero` · goal: `rexp (-0 * c)` → `1` -/
example (c : ℝ) (P : ℝ → Prop) (h : P 1) : P (rexp (-0 * c)) := by
  rw [neg_zero]
  rw [zero_mul]
  rw [Real.exp_zero]
  exact h

/-! ### R9. `Finset.sum_const`, `Finset.card_univ`, `nsmul_eq_mul`, `mul_one` · goal: `∑ j : ι, 1` → `↑(card ι)` -/
example {ι : Type} [Fintype ι] (P : ℝ → Prop) (h : P ↑(Fintype.card ι)) :
    P (∑ _j : ι, (1 : ℝ)) := by
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [nsmul_eq_mul]
  rw [mul_one]
  exact h

/-! ### R10. `one_div` · `1 / a = a⁻¹` · goal: `simp` writes every `1 / a` as `a⁻¹` -/
example {G : Type} [DivInvMonoid G] (a : G) (P : G → Prop) (h : P a⁻¹) : P (1 / a) := by
  rw [one_div]
  exact h

/-! ### R11. `simpa [d₁, d₂] using e` · closes the goal: simp `e`'s type and the goal, then match -/
noncomputable def q (x : ℝ) : ℝ := 1 / (x * 1)

example (a : ℝ) (P : ℝ → Prop) (e : P (q a)) : P a⁻¹ := by
  simpa [q] using e

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Continuity of a quotient: R3, then R4 twice, then a positivity fact flipped by R6
`Real.exp_pos x : 0 < rexp x`. -/
example : Continuous fun x : ℝ => rexp (2 * x) / rexp x := by
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro x
    exact (Real.exp_pos x).ne'

/-! ### W2. `exact` sees through a definition, `rw` does not
`Zt x` and `1 + rexp x` are the same term once `Zt` is unfolded, so `h.ne'` closes the goal. -/
noncomputable def Zt (x : ℝ) : ℝ := 1 + rexp x

example (x : ℝ) (h : 0 < Zt x) : 1 + rexp x ≠ 0 := by
  exact h.ne'

/-! ### W3. A limit at `0` by continuity: a `have`, then R7 inside `simpa` (R8, R10, R11) -/
example : Tendsto (fun x : ℝ => rexp (-x * 3) / 2) (𝓝 0) (𝓝 (1 / 2)) := by
  have hc : Continuous fun x : ℝ => rexp (-x * 3) / 2 := by fun_prop
  have ht := hc.tendsto 0
  simpa using ht

end M154Guide

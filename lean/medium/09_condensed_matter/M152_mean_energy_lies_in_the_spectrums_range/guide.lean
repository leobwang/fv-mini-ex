/- Guide for M152 (Mean energy lies in the spectrum's range).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is a goal the step leaves alone; `g` is only there to finish the example.
Part W: worked combinations on weights `w` that are NOT the exercise's (no ensemble).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M152Guide

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]

/-! # Part R · Reference entries -/

/-! ## The weights `p_t(k)`: positive, summing to 1 -/

/-! ### R1. `mathematicalPartitionFunctionBetaReal_pos` · context gains `0 < Z(t)`
Needs `[Nonempty ι]`: a sum of positive terms over a nonempty finite set is positive. -/
example [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)
    (g : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t → G) : G := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos t
  exact g hZ

/-! ### R2. `unfold probabilityBetaReal` · goal: the name `p` → its body `rexp (-t * E k) / Z(t)`
`simp only [probabilityBetaReal]` does the same. -/
example (𝓒 : CanonicalEnsemble ι) (t : ℝ) (k : ι) (P : ℝ → Prop)
    (h : P (rexp (-t * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal t)) :
    P (𝓒.probabilityBetaReal t k) := by
  unfold probabilityBetaReal
  exact h

/-! ### R3. `positivity` · closes `0 ≤ e` / `0 < e` built from `rexp`, `/`, `*`, `+`, squares …
It knows `0 < rexp x`. For an atom it cannot see into (here `c`), it uses a hypothesis
`0 < c` or `0 ≤ c` from the context; without `hc` it fails. -/
example (x c : ℝ) (hc : 0 < c) : 0 ≤ rexp x / c := by
  positivity

/-! ### R4. `Finset.sum_div` · `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; `←` pulls a common divisor out
`∑ i, …` (no `∈ s`) is the sum over `Finset.univ`, all of `ι`. -/
example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) / a)) : P (∑ i, f i / a) := by
  rw [← Finset.sum_div]
  exact h

/-! ### R5. `LT.lt.ne'` (dot notation `hab.ne'`) · `a < b → b ≠ a`; context gains `b ≠ a`
From `hZ : 0 < Z` it gives `hZ.ne' : Z ≠ 0`, the form `div_self` asks for. -/
example {α : Type} [Preorder α] (a b : α) (hab : a < b) (G : Prop) (g : b ≠ a → G) : G := by
  have h := hab.ne'
  exact g h

/-! ### R6. `div_self` · `a ≠ 0 → a / a = 1` · goal -/
example (a : ℝ) (ha : a ≠ 0) (P : ℝ → Prop) (h : P 1) : P (a / a) := by
  rw [div_self ha]
  exact h

/-! ### R7. `exact` up to unfolding a definition · closes `e / Z = 1` when `Z` is *defined* as `e`
`rw` matches syntax, `exact` matches definitions: `rw [div_self hZ.ne']` cannot see that the
numerator is `Z`, but `exact div_self hZ.ne'` unfolds `Z` and succeeds. -/
noncomputable def Zw (w : ι → ℝ) : ℝ := ∑ i, w i
example (w : ι → ℝ) (hZ : Zw w ≠ 0) : (∑ i, w i) / Zw w = 1 := by
  exact div_self hZ

/-! ## The mean `U = ∑ E i * p i` -/

/-! ### R8. `unfold meanEnergyBetaReal` · goal: the name `U` → its body `∑ i, E i * p_t(i)` -/
example (𝓒 : CanonicalEnsemble ι) (t : ℝ) (P : ℝ → Prop)
    (h : P (∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal t i)) : P (𝓒.meanEnergyBetaReal t) := by
  unfold meanEnergyBetaReal
  exact h

/-! ### R9. `calc` mixing `=` and `≤` · goal list: `x ≤ z` → one goal per step
`x = y` then `y ≤ z` gives `x ≤ z`. A step may write `_` for a side Lean takes from the goal.
Each `?_` becomes a goal `case calc_k`; normally you write `:= by tac` or `:= term` instead. -/
example (x y z : ℝ) (h₁ : x = y) (h₂ : y ≤ z) : x ≤ z := by
  calc x = y := ?_
    _ ≤ z := ?_
  exact h₁
  exact h₂

/-! ### R10. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `←` pulls a common factor out -/
example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (a * ∑ i, f i)) : P (∑ i, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R11. `mul_one` · `a * 1 = a` · goal -/
example {α : Type} [MulOneClass α] (a : α) (P : α → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R12. `Finset.sum_le_sum` · goal `∑ f ≤ ∑ g` → `∀ i ∈ univ, f i ≤ g i` (term by term) -/
example (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) : ∑ i, f i ≤ ∑ i, g i := by
  apply Finset.sum_le_sum
  intro i _
  exact h i

/-! ### R13. `mul_le_mul_of_nonneg_right` · `b ≤ c → 0 ≤ a → b * a ≤ c * a` · goal → two goals
Multiplying an inequality on the right by a non-negative `a` keeps it. -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) : b * a ≤ c * a := by
  apply mul_le_mul_of_nonneg_right
  exact hbc
  exact ha

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Normalising positive weights: R4 → R7 (with R5) -/
example (w : ι → ℝ) (hS : 0 < Zw w) : ∑ i, w i / Zw w = 1 := by
  rw [← Finset.sum_div]
  exact div_self hS.ne'

/-! ### W2. A constant times total weight 1: R10 → `rw [h1]` → R11 -/
example (w : ι → ℝ) (h1 : ∑ i, w i = 1) : ∑ i, 3 * w i = 3 := by
  rw [← Finset.mul_sum]
  rw [h1]
  rw [mul_one]

/-! ### W3. Values below 1 weigh no more than the weights: R12 → R13, then `one_mul` -/
example (x w : ι → ℝ) (hx : ∀ i, x i ≤ 1) (hw : ∀ i, 0 ≤ w i) : ∑ i, x i * w i ≤ ∑ i, w i := by
  calc ∑ i, x i * w i ≤ ∑ i, 1 * w i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i) (hw i)
    _ = ∑ i, w i := by simp only [one_mul]

end M152Guide

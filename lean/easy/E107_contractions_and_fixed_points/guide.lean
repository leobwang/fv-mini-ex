/- Guide for E107 (Contractions and fixed points).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on a map that is NOT the exercise's (`x / 2 - 3`).
Assumed: Lean basics.
-/
import Mathlib

namespace E107Guide

/-! # Part R · Reference entries -/

/-! ## Lipschitz: from `edist` to `dist` to `|·|` -/

/-! ### R1. `LipschitzWith.of_dist_le_mul` · goal `LipschitzWith K f` → context gains `x y`, goal a `dist` bound
`refine LipschitzWith.of_dist_le_mul fun x y => ?_` names the two points `x y`. -/
example {α β : Type} [PseudoMetricSpace α] [PseudoMetricSpace β] (K : NNReal) (f : α → β)
    (h : ∀ x y, dist (f x) (f y) ≤ ↑K * dist x y) : LipschitzWith K f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  exact h x y

/-! ### R2. `Real.dist_eq` · goal: `dist a b` → `|a - b|` on `ℝ`
Use `simp only [Real.dist_eq]`: it rewrites every `dist`, each with its own arguments. -/
example (a b c d : ℝ) (P : ℝ → ℝ → Prop) (h : P |a - b| |c - d|) : P (dist a b) (dist c d) := by
  simp only [Real.dist_eq]
  exact h

/-! ## The constant: casting `NNReal` numerals into `ℝ` -/

/-! ### R3. `NNReal.coe_div` · goal: `↑(r₁ / r₂)` → `↑r₁ / ↑r₂` (the cast `NNReal → ℝ` moves inside `/`) -/
example (r₁ r₂ : NNReal) (P : ℝ → Prop) (h : P (↑r₁ / ↑r₂)) : P ↑(r₁ / r₂) := by
  simp only [NNReal.coe_div]
  exact h

/-! ### R4. `NNReal.coe_one` · goal: `↑1` (the `NNReal` one, cast) → `1 : ℝ` -/
example (P : ℝ → Prop) (h : P 1) : P ((1 : NNReal) : ℝ) := by
  simp only [NNReal.coe_one]
  exact h

/-! ### R5. `NNReal.coe_ofNat` · goal: `↑2` (an `NNReal` numeral `≥ 2`, cast) → `2 : ℝ` -/
example (P : ℝ → Prop) (h : P 2) : P ((2 : NNReal) : ℝ) := by
  simp only [NNReal.coe_ofNat]
  exact h

/-! ## Reshaping the difference -/

/-! ### R6. `rw [show e₁ = e₂ by ring]` · goal: `e₁` → `e₂`, for an identity you prove on the spot -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P ((a - b) / c)) : P (a / c - b / c) := by
  rw [show a / c - b / c = (a - b) / c by ring]
  exact h

/-! ### R7. `abs_div` · goal: `|a / b|` → `|a| / |b|` -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) (P : α → Prop)
    (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R8. `abs_two` · goal: `|2|` → `2` -/
example {α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (P : α → Prop) (h : P 2) : P |2| := by
  rw [abs_two]
  exact h

/-! ### R9. `linarith` · closes a linear (in)equality; `|x - y|` counts as one unknown -/
example (x y : ℝ) : |x - y| / 3 ≤ 1 / 3 * |x - y| := by linarith

/-! ## Contractions -/

/-! ### R10. `ContractingWith K f` is `K < 1 ∧ LipschitzWith K f` · goal → two goals
As a term: `⟨hK, hf⟩`. -/
example {α : Type} [EMetricSpace α] (K : NNReal) (f : α → α) (hK : K < 1)
    (hf : LipschitzWith K f) : ContractingWith K f := by
  refine ⟨?_, ?_⟩
  exact hK
  exact hf

/-! ### R11. `norm_num` · closes a numeral goal, in `NNReal` as in `ℝ` -/
example : (1 / 3 : NNReal) < 1 := by norm_num

/-! ## Fixed points -/

/-! ### R12. `Function.IsFixedPt f x` is `f x = x` · `simp only [Function.IsFixedPt]` unfolds it
`norm_num [Function.IsFixedPt]` unfolds and computes in one step. -/
example {α : Type} (f : α → α) (x : α) (h : f x = x) : Function.IsFixedPt f x := by
  simp only [Function.IsFixedPt]
  exact h

/-! # Part W · Worked combinations (the map `x ↦ x / 2 - 3`, not the exercise's) -/

/-! ### W1. Lipschitz with constant `1/2`: R1, R2–R5, R6, R7, R8, R9 -/
theorem w_lipschitz : LipschitzWith (1 / 2) (fun x : ℝ => x / 2 - 3) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [show x / 2 - 3 - (y / 2 - 3) = (x - y) / 2 by ring]
  rw [abs_div, abs_two]
  linarith

/-! ### W2. A contraction from the Lipschitz fact: R10 as a term, R11 for `1 / 2 < 1` -/
example : ContractingWith (1 / 2) (fun x : ℝ => x / 2 - 3) := ⟨by norm_num, w_lipschitz⟩

/-! ### W3. `-6` is a fixed point: R12, then R11 -/
example : Function.IsFixedPt (fun x : ℝ => x / 2 - 3) (-6) := by
  simp only [Function.IsFixedPt]
  norm_num

end E107Guide

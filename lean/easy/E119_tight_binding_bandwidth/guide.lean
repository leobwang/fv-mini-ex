/- Guide for E119 (Tight-binding bandwidth).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: a worked combination on an expression that is NOT the exercise's (no `E0`, no `2`, no `-`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace E119Guide

/-! # Part R · Reference entries -/

/-! ## From the energy to an algebraic expression -/

/-! ### R1. `unfold TightBindingChain.energyEigenvalue` · goal: the name → its formula
`T.energyEigenvalue k` is defined as `T.E0 - 2 * T.t * Real.cos (↑k * T.a)`; `↑k : ℝ` is the value of
`k`, an element of the set `T.QuantaWaveNumber` of allowed wavenumbers. -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (P : ℝ → Prop)
    (h : P (T.E0 - 2 * T.t * Real.cos (↑k * T.a))) : P (T.energyEigenvalue k) := by
  unfold TightBindingChain.energyEigenvalue
  exact h

/-! ### R2. `rw [show e₁ = e₂ by ring]` · goal: an algebraic rearrangement `e₁` → `e₂`
`show e₁ = e₂ by ring` is a proof term of `e₁ = e₂` built on the spot; `rw` then uses it. `e₁` must
appear literally in the goal, so copy it from the infoview (write `↑k` as `k`: Lean re-inserts the cast). -/
example {α : Type} [CommRing α] (a b : α) (P : α → Prop) (h : P (-b)) : P (a - b - a) := by
  rw [show a - b - a = -b by ring]
  exact h

/-! ## Absolute values -/

/-! ### R3. `abs_neg` · `|-a| = |a|` · goal
Lean prints `|-x|` as `|(-x)|`. `[Lattice α] [AddGroup α]`: `ℝ` qualifies. -/
example {α : Type} [Lattice α] [AddGroup α] (a : α) (P : α → Prop) (h : P |a|) : P |-a| := by
  rw [abs_neg]
  exact h

/-! ### R4. `abs_mul` · `|a * b| = |a| * |b|` · goal
`*` groups to the left: `|x * y * z|` is `|(x * y) * z|`, so one `rw` splits off only the last factor. -/
example {α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (a b : α) (P : α → Prop)
    (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R5. `abs_two` · `|2| = 2` · goal -/
example {α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (P : α → Prop) (h : P 2) :
    P |(2 : α)| := by
  rw [abs_two]
  exact h

/-! ## Bounding a product -/

/-! ### R6. `apply mul_le_of_le_one_right` · `0 ≤ a → b ≤ 1 → a * b ≤ a` · goal → two goals
A factor `b` at most `1` does not increase a nonnegative `a`. `exact mul_le_of_le_one_right h0 h1`
does both goals at once. -/
example {α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (a b : α) (h0 : 0 ≤ a)
    (h1 : b ≤ 1) : a * b ≤ a := by
  apply mul_le_of_le_one_right
  exact h0
  exact h1

/-! ### R7. `positivity` · closes `0 ≤ e` (or `0 < e`) when `e` is built from nonnegative pieces
Numerals, `|x|`, squares, sums and products of such. Writable inline as `(by positivity)`. -/
example (x y : ℝ) : 0 ≤ 3 * |x| * |y| := by positivity

/-! ### R8. `Real.abs_cos_le_one` · `|Real.cos x| ≤ 1` · closes the goal (with `exact`) -/
example (x : ℝ) : |Real.cos x| ≤ 1 := by
  exact Real.abs_cos_le_one x

/-! # Part W · Worked combination (not the exercise's expression) -/

/-! ### W1. `|c + b * cos x - c| ≤ |b|`: R2, R4, then R6 with R7 and R8 as its two arguments -/
example (b c x : ℝ) : |c + b * Real.cos x - c| ≤ |b| := by
  rw [show c + b * Real.cos x - c = b * Real.cos x by ring]
  rw [abs_mul]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one x)

end E119Guide

/- Guide for M174 (The Lorentz factor is at least 1).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the bound `3`, the radicand `x / 2`).
Assumed: Lean basics.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Basic

open LorentzGroup

namespace M174Guide

/-! # Part R · Reference entries -/

/-! ## From the matrix entry to a real number -/

/-! ### R1. `rw [boost_inl_0_inl_0]` · `↑(boost i β hβ) (Sum.inl 0) (Sum.inl 0) = γ β` · goal
`↑Λ` (written `Λ.1`) is the matrix of `Λ : LorentzGroup d`; `Sum.inl 0` is the time index. -/
example {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (P : ℝ → Prop) (h : P (γ β)) :
    P ((boost i β hβ).1 (Sum.inl 0) (Sum.inl 0)) := by
  rw [boost_inl_0_inl_0]
  exact h

/-! ### R2. `unfold γ` · goal: `γ β` → its definition `1 / √(1 - β ^ 2)` -/
example (β : ℝ) (P : ℝ → Prop) (h : P (1 / √(1 - β ^ 2))) : P (γ β) := by
  unfold γ
  exact h

/-! ## Facts about `β` -/

/-! ### R3. `abs_lt.mp` · `abs_lt : |a| < b ↔ -b < a ∧ a < b` · context gains the two bounds
`.mp` uses an `↔` left to right: from a proof of `|a| < b` it builds a proof of `-b < a ∧ a < b`. -/
example (a b : ℝ) (hab : |a| < b) (P : Prop) (k : -b < a ∧ a < b → P) : P := by
  have h := abs_lt.mp hab
  exact k h

/-! ### R4. `sq_nonneg a` · `0 ≤ a ^ 2` · context gains the fact (a hint for `nlinarith`) -/
example (a : ℝ) (P : Prop) (k : 0 ≤ a ^ 2 → P) : P := by
  have h := sq_nonneg a
  exact k h

/-! ### R5. `nlinarith [t₁, t₂]` · closes a polynomial (in)equality over `ℝ`
The terms `tᵢ` are extra facts it may use; it splits `∧`, multiplies pairs of facts, then runs
linear arithmetic. Here it multiplies `0 < 2 + a` by `0 < 2 - a`. -/
example (a : ℝ) (hab : -2 < a ∧ a < 2) : 0 < 4 - a ^ 2 := by
  nlinarith [hab.1, hab.2]

/-! ## Square roots and `1 ≤ a / b` -/

/-! ### R6. `Real.sqrt_pos.mpr` · `Real.sqrt_pos : 0 < √x ↔ 0 < x` · context gains `0 < √x`
`.mpr` uses an `↔` right to left: from `0 < x` it builds `0 < √x`. -/
example (x : ℝ) (hx : 0 < x) (P : Prop) (k : 0 < √x → P) : P := by
  have h := Real.sqrt_pos.mpr hx
  exact k h

/-! ### R7. `rw [one_le_div hb]` · `one_le_div : 0 < b → (1 ≤ a / b ↔ b ≤ a)` · goal
`rw` with an `↔` replaces the proposition `1 ≤ a / b` by `b ≤ a`; `hb : 0 < b` is its premise. -/
example (a b : ℝ) (hb : 0 < b) (h : b ≤ a) : 1 ≤ a / b := by
  rw [one_le_div hb]
  exact h

/-! ### R8. `apply Real.sqrt_le_one.mpr` · `Real.sqrt_le_one : √x ≤ 1 ↔ x ≤ 1` · goal: `√x ≤ 1` → `x ≤ 1` -/
example (x : ℝ) (h : x ≤ 1) : √x ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A strict bound from `|a| < 3`: R3 inside R5 -/
example (a : ℝ) (ha : |a| < 3) : 0 < 9 - a ^ 2 := by
  nlinarith [abs_lt.mp ha]

/-! ### W2. `1 ≤ 1 / √(x / 2)` for `0 < x ≤ 2`: R6 → R7 → R8, then linear arithmetic -/
example (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 2) : 1 ≤ 1 / √(x / 2) := by
  have hpos : 0 < x / 2 := by linarith
  rw [one_le_div (Real.sqrt_pos.mpr hpos)]
  apply Real.sqrt_le_one.mpr
  linarith

end M174Guide

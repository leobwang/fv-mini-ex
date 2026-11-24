/- Guide for M072 (AM-GM for two reals).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `g` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M072Guide

/-! # Part R · Reference entries -/

/-! ## Polynomial inequalities -/

/-! ### R1. `sq_nonneg e` · `0 ≤ e ^ 2` · `have h := sq_nonneg e`: context gains `h`; goal unchanged -/
example (e : ℝ) (G : Prop) (g : 0 ≤ e ^ 2 → G) : G := by
  have h := sq_nonneg e
  exact g h

/-! ### R2. `nlinarith [t₁, …]` · closes a polynomial (in)equality that follows from the hypotheses,
the extra facts `tᵢ`, and their pairwise products -/
example (x : ℝ) : 0 ≤ x ^ 2 - 6 * x + 10 := by
  nlinarith [sq_nonneg (x - 3)]

/-! ## Square roots -/

/-! ### R3. `rw [show s = t from proof]` · goal: every `s` → `t`, with a one-off equation -/
example (s t : ℝ) (hst : s = t) (P : ℝ → Prop) (h : P t) : P s := by
  rw [show s = t from hst]
  exact h

/-! ### R4. `Real.sqrt_sq` · `0 ≤ x → √(x ^ 2) = x` · goal: `√(x ^ 2)` → `x` -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (√(x ^ 2)) := by
  rw [Real.sqrt_sq hx]
  exact h

/-! ### R5. `hst.symm` (`Eq.symm`) · from `hst : s = t` get `t = s` · context gains `h : t = s` -/
example {α : Type} (s t : α) (hst : s = t) (G : Prop) (g : t = s → G) : G := by
  have h := hst.symm
  exact g h

/-! ### R6. `positivity` · closes `0 ≤ e` / `0 < e` built from `+ * / ^`, numerals and variables
with a hypothesis `0 ≤ x` in the context -/
example (x y : ℝ) (hx : 0 ≤ x) : 0 ≤ (x + y ^ 2) / 3 := by
  positivity

/-! ### R7. `Real.sqrt_le_sqrt` · `x ≤ y → √x ≤ √y` · `apply` it: goal `√x ≤ √y` → `x ≤ y` -/
example (x y : ℝ) (hxy : x ≤ y) : √x ≤ √y := by
  apply Real.sqrt_le_sqrt
  exact hxy

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Several squares as hints: the sum of three R1 facts gives a three-variable bound -/
example (x y z : ℝ) : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-! ### W2. Bound a square root: write the right side as a root (R3, R4, R5), then R7 -/
example (u v : ℝ) (hv : 0 ≤ v) (huv : u ≤ v ^ 2) : √u ≤ v := by
  rw [show v = √(v ^ 2) from (Real.sqrt_sq hv).symm]
  exact Real.sqrt_le_sqrt huv

/-! ### W3. The side condition of R4 proved on the spot by R6 -/
example (x y : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P ((x + y ^ 2) / 3)) :
    P (√(((x + y ^ 2) / 3) ^ 2)) := by
  rw [Real.sqrt_sq (by positivity)]
  exact h

end M072Guide

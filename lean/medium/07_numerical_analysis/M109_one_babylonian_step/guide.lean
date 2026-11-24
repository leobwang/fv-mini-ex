/- Guide for M109 (One Babylonian step).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g`) in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`1/y - 1/(y+1)`, `√3`, `1/y ≤ y`).
Assumed: Lean basics (E001–E033). Generic tactics (`have`, `rw`, `exact`) are in TACTIC_STATES.md.
-/
import Mathlib

namespace M109Guide

/-! # Part R · Reference entries -/

/-! ## Unfolding a definition and square-root facts -/

/-! ### R1. `unfold f` · goal: the defined name `f u v` → its body
Division on `ℝ` is not computable, so a definition using it must be marked `noncomputable`. -/
noncomputable def mid (u v : ℝ) : ℝ := (u + v) / 2
example (u v : ℝ) (P : ℝ → Prop) (h : P ((u + v) / 2)) : P (mid u v) := by
  unfold mid
  exact h

/-! ### R2. `Real.sq_sqrt` · `0 ≤ b → √b ^ 2 = b` · `have hs := Real.sq_sqrt hb`: context gains `hs` -/
example (b : ℝ) (hb : 0 ≤ b) (G : Prop) (g : √b ^ 2 = b → G) : G := by
  have hs := Real.sq_sqrt hb
  exact g hs

/-! ### R3. `field_simp` · goal: an equation with denominators → one without (cross-multiplied)
It must know each denominator is `≠ 0`; a hypothesis `hw : 0 < w` (or `w ≠ 0`) in the context suffices.
The exact shape of the result is `field_simp`'s choice: read it off the infoview. -/
example (u v w : ℝ) (hw : 0 < w) (h : u * w + v = w * 3) : u + v / w = 3 := by
  field_simp
  exact h

/-! ### R4. `nlinarith [t₁, t₂]` · closes a polynomial (in)equality over `ℝ`
`linarith` (R6) plus products: it also multiplies pairs of hypotheses and of the hint terms `tᵢ`.
Here it uses the square fact `hs` to replace `s ^ 2` by `b`. -/
example (s b : ℝ) (hs : s ^ 2 = b) : (1 + s) ^ 2 = 1 + 2 * s + b := by
  nlinarith [hs]

/-! An inequality: it multiplies `0 ≤ s` and `s ≤ y` to get the product terms it needs. -/
example (s y : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ y) : s * s ≤ y * y := by
  nlinarith [h0, h1]

/-! ## Signs and linear arithmetic -/

/-! ### R5. `positivity` · closes `0 ≤ e` or `0 < e` when `e` is built from nonnegative pieces
Squares are `≥ 0`; a quotient or product of nonnegatives is `≥ 0`; `t` is `> 0` by `ht` in context. -/
example (u t : ℝ) (ht : 0 < t) : 0 ≤ (u + t) ^ 2 / (5 * t) := by
  positivity

/-! ### R6. `linarith` · closes a linear (in)equality that follows from the context
Any nonlinear piece (`p / q`, `e ^ 2`, a product of variables) is treated as one opaque unknown. -/
example (p q r : ℝ) (h1 : p - q = r) (h2 : 0 ≤ r) : q ≤ p := by
  linarith

/-! ## Inequalities with a division -/

/-! ### R7. `div_le_iff₀` · `0 < c → (b / c ≤ a ↔ b ≤ a * c)` · goal: clear a positive denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : b ≤ a * c) : b / c ≤ a := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R8. `Real.sqrt_nonneg` · `0 ≤ √b` for every `b`, no hypothesis · context gains it -/
example (b : ℝ) (G : Prop) (g : 0 ≤ √b → G) : G := by
  have hn := Real.sqrt_nonneg b
  exact g hn

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Clear denominators, then close the polynomial identity: R3, then `ring` -/
example (y : ℝ) (hy : 0 < y) : 1 / y - 1 / (y + 1) = 1 / (y * (y + 1)) := by
  field_simp
  ring

/-! ### W2. A polynomial identity modulo a square-root fact: R2, then R4 -/
example : (√3 - 1) ^ 2 = 4 - 2 * √3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith [hs]

/-! ### W3. A sign fact as a `have`, then linear arithmetic: R5, then R6 -/
example (y s E : ℝ) (hy : 0 < y) (hE : E - s = (y - s) ^ 4 / y) : s ≤ E := by
  have hq : 0 ≤ (y - s) ^ 4 / y := by positivity
  linarith

/-! ### W4. An inequality with a division: R7, then R4 -/
example (y : ℝ) (hy : 0 < y) (h1 : 1 ≤ y) : 1 / y ≤ y := by
  rw [div_le_iff₀ hy]
  nlinarith [h1]

end M109Guide

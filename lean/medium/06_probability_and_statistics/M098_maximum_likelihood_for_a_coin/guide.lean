/- Guide for M098 (Maximum likelihood for a coin).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other weights, other casts).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M098Guide

/-! # Part R · Reference entries -/

/-! ## Facts about casts `ℕ → ℝ` -/

/-! ### R1. `exact_mod_cast h` · closes a goal that is `h` with casts `↑` added or removed -/
example (a b : ℕ) (h : a < b) : (a : ℝ) < b := by
  exact_mod_cast h

/-! ### R2. `h₁.trans h₂` (lemma `lt_trans`) · proof term: `a < b` and `b < c` give `a < c` -/
example (a b c : ℕ) (h₁ : a < b) (h₂ : b < c) : a < c := by
  exact h₁.trans h₂

/-! ### R3. `h.le` (lemma `le_of_lt`) · proof term: `a < b` gives `a ≤ b` -/
example (a b : ℕ) (h : a < b) : a ≤ b := by
  exact h.le

/-! ### R4. `Nat.cast_sub` · `m ≤ n → ↑(n - m) = ↑n - ↑m` · goal: cast of a ℕ-difference → difference of casts -/
example (m n : ℕ) (hmn : m ≤ n) (P : ℝ → Prop) (h : P ((n : ℝ) - m)) : P ((n - m : ℕ) : ℝ) := by
  rw [Nat.cast_sub hmn]
  exact h

/-! ## Positivity side facts -/

/-! ### R5. `sub_pos` · `0 < a - b ↔ b < a` · goal: `0 < a - b` → `b < a` -/
example (a b : ℝ) (h : b < a) : 0 < a - b := by
  rw [sub_pos]
  exact h

/-! ### R6. `positivity` · closes `0 < e` / `0 ≤ e` built from `+ * / ^`, using hypotheses `0 < x` on atoms -/
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x / y := by
  positivity

/-! ### R7. `div_lt_one` · `0 < b → (a / b < 1 ↔ a < b)` · goal: `a / b < 1` → `a < b` -/
example (a b : ℝ) (hb : 0 < b) (h : a < b) : a / b < 1 := by
  rw [div_lt_one hb]
  exact h

/-! ## The Gibbs bound `log x ≤ x - 1` -/

/-! ### R8. `Real.log_le_sub_one_of_pos` · `0 < x → Real.log x ≤ x - 1` · context gains the bound -/
example (x : ℝ) (hx : 0 < x) (G : Prop) (h : Real.log x ≤ x - 1 → G) : G := by
  have g := Real.log_le_sub_one_of_pos hx
  exact h g

/-! ### R9. `div_pos` · `0 < a → 0 < b → 0 < a / b` · context gains `0 < a / b` -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (G : Prop) (h : 0 < a / b → G) : G := by
  have hab := div_pos ha hb
  exact h hab

/-! ### R10. `sub_pos.mpr h` (`Iff.mpr`) · proof term: use an `↔` right to left; `b < a` gives `0 < a - b` -/
example (a b : ℝ) (hba : b < a) (G : Prop) (h : 0 < a - b → G) : G := by
  have hab := sub_pos.mpr hba
  exact h hab

/-! ### R11. `h.ne'` (lemma `LT.lt.ne'`) · proof term: `0 < a` gives `a ≠ 0` -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (h : a ≠ 0 → G) : G := by
  have ha' := ha.ne'
  exact h ha'

/-! ### R12. `rw [Real.log_div hx hy] at g` · `x ≠ 0 → y ≠ 0 → Real.log (x / y) = Real.log x - Real.log y`
· context: hypothesis `g` is rewritten, the goal is untouched -/
example (x y c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (g : Real.log (x / y) ≤ c) :
    Real.log x - Real.log y ≤ c := by
  rw [Real.log_div hx hy] at g
  exact g

/-! ## Algebra: clearing denominators -/

/-! ### R13. `field_simp` · goal: multiplies out every denominator it can prove `≠ 0`
(from hypotheses `_ ≠ 0` in the context, or numerals) -/
example (a b c : ℝ) (hb : b ≠ 0) (h : a + b * c = b) : a / b + c = 1 := by
  field_simp
  exact h

/-! ## Assembling the inequality -/

/-! ### R14. `unfold f` · goal: the defined name `f` → its body -/
noncomputable def f (x : ℝ) : ℝ := 2 * Real.log x
example (x : ℝ) (P : ℝ → Prop) (h : P (2 * Real.log x)) : P (f x) := by
  unfold f
  exact h

/-! ### R15. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · proof term: scale an inequality -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) (G : Prop) (h : a * b ≤ a * c → G) : G := by
  have hs := mul_le_mul_of_nonneg_left hbc ha
  exact h hs

/-! ### R16. `nlinarith [t₁, t₂]` · closes a goal `≤ < =` that follows linearly from the context plus the
listed terms `tᵢ` (and products of pairs of them); products like `a * Real.log x` are treated as atoms.
`linarith [t₁, t₂]` is the same without the pairwise products (enough when no product is needed). -/
example (a x y : ℝ) (h₁ : a * x ≤ a * y) (h₂ : a * y = 0) : a * x ≤ 0 := by
  nlinarith [h₁, h₂]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A cast fact for a ℕ-difference: R4, then R5, then R1 -/
example (a b : ℕ) (hab : a < b) : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by
  rw [Nat.cast_sub hab.le]
  rw [sub_pos]
  exact_mod_cast hab

/-! ### W2. One weighted Gibbs bound `w log (x / w) ≤ x - w` for `w, x > 0`: R9, R8, R13, R3, R15, R16
`field_simp` finds `w ≠ 0` from `hw : 0 < w` by itself. -/
example (w x : ℝ) (hw : 0 < w) (hx : 0 < x) : w * Real.log (x / w) ≤ x - w := by
  have g := Real.log_le_sub_one_of_pos (div_pos hx hw)
  have e : w * (x / w - 1) = x - w := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left g hw.le]

/-! ### W3. `log` of a quotient inside a hypothesis, then combine: R12, R16 -/
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (g : Real.log (x / y) ≤ 0) : Real.log x ≤ Real.log y := by
  rw [Real.log_div hx.ne' hy.ne'] at g
  linarith

end M098Guide

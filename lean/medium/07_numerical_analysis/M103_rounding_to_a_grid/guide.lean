/- Guide for M103 (Rounding to a grid).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α]` reads "α is an ordered field": ℚ and ℝ are.
Part W: worked combinations on objects that are NOT the exercise's (other grids, other powers of 2).
Assumed: Lean basics.
-/
import Mathlib

namespace M103Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 tools: unfolding, clearing denominators, absolute values -/

/-! ### R1. `unfold D` · goal: the name `D` → its body
`round y : ℤ` is the integer nearest to `y`; `↑(round y)` is that integer cast back into ℝ. -/
noncomputable def snap (y : ℝ) : ℝ := 3 * round y
example (P : ℝ → Prop) (y : ℝ) (h : P (3 * ↑(round y))) : P (snap y) := by
  unfold snap
  exact h

/-! ### R2. `field_simp` · goal: divisions cleared, using `c ≠ 0` (found from `hc : 0 < c`) -/
example (a b c : ℝ) (hc : 0 < c) (h : a = c * b) : a / c = b := by
  field_simp
  exact h

/-! ### R3. `abs_neg` · `|-a| = |a|` · goal -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a : α) (P : α → Prop)
    (h : P |a|) : P |-a| := by
  rw [abs_neg]
  exact h

/-! ### R4. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) (P : α → Prop)
    (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R5. `abs_of_pos` · `0 < a → |a| = a` · goal; give the positivity proof: `abs_of_pos ha` -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a : α) (ha : 0 < a)
    (P : α → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ### R6. `abs_sub_round` · `|y - round y| ≤ 1 / 2` · context gains the bound
`[FloorRing α]`: α has `⌊·⌋`, hence `round`; ℚ and ℝ do. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] (y : α)
    (G : Prop) (h : |y - round y| ≤ 1 / 2 → G) : G := by
  have hr := abs_sub_round y
  exact h hr

/-! ### R7. `nlinarith [t₁, …]` · closes a (nonlinear) inequality
It multiplies pairs of hypotheses and hint terms `tᵢ`, then does linear arithmetic. A hint can be a
lemma applied to arguments (`hf t`), so the fact need not be in the context. -/
example (a t : ℝ) (f : ℝ → ℝ) (ha : 0 < a) (hf : ∀ s, f s ≤ 3) : a * f t ≤ 3 * a := by
  nlinarith [hf t]

/-! ## Part 2 tools: positivity, witnesses, division, integer powers -/

/-! ### R8. `lt_of_lt_of_le` · `a < b → b ≤ c → a < c` · closes the goal (term) -/
example {α : Type} [Preorder α] (a b c : α) (hab : a < b) (hbc : b ≤ c) : a < c := by
  exact lt_of_lt_of_le hab hbc

/-! ### R9. `positivity` · closes `0 < t` / `0 ≤ t` / `t ≠ 0` built from positive pieces
`2 ^ k` with `k : ℤ` is an integer power (`zpow`): `2 ^ (-1) = 1 / 2`. -/
example (k : ℤ) (y : ℝ) (hy : 0 < y) : (0 : ℝ) < 2 ^ k * y := by
  positivity

/-! ### R10. `refine ⟨w, ?_, ?_⟩` · goal `∃ δ, A δ ∧ B δ` → goals `A w` and `B w` -/
example (A B : ℝ → Prop) (w : ℝ) (ha : A w) (hb : B w) : ∃ δ, A δ ∧ B δ := by
  refine ⟨w, ?_, ?_⟩
  exacts [ha, hb]

/-! ### R11. `have hk := thm args (by tac)` · context gains `thm`'s conclusion at those arguments
A theorem proved earlier in the file is used like this; `(by positivity)` fills its `0 < _` argument. -/
example (f : ℝ → ℝ) (hf : ∀ s : ℝ, 0 < s → f s ≤ s / 2) (k : ℤ) (G : Prop)
    (h : f (2 ^ k) ≤ 2 ^ k / 2 → G) : G := by
  have hk := hf (2 ^ k) (by positivity)
  exact h hk

/-! ### R12. `abs_div` · `|a / b| = |a| / |b|` · goal -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) (P : α → Prop)
    (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R13. `div_le_iff₀` · `0 < c → (b / c ≤ a ↔ b ≤ a * c)` · goal: the division leaves -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α) (hc : 0 < c)
    (h : b ≤ a * c) : b / c ≤ a := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R14. `rw [show s = t by ring]` · goal: rewrite with an equation proved on the spot
`(n : ℤ)` casts the natural number `n` into ℤ; Lean prints it `↑n`. `ring` proves the ℤ identity. -/
example (m : ℤ) (n : ℕ) (P : ℤ → Prop) (h : P (m - 1 + (↑n + 1))) : P (m + ↑n) := by
  rw [show m + (n : ℤ) = m - 1 + (n + 1) by ring]
  exact h

/-! ### R15. `zpow_add₀` · `a ≠ 0 → a ^ (m + n) = a ^ m * a ^ n` (`m n : ℤ`) · goal
`[GroupWithZero α]`: α has `*`, `0` and `⁻¹` with `a * a⁻¹ = 1` for `a ≠ 0`; ℚ, ℝ, ℂ do. -/
example {α : Type} [GroupWithZero α] (a : α) (ha : a ≠ 0) (m n : ℤ) (P : α → Prop)
    (h : P (a ^ m * a ^ n)) : P (a ^ (m + n)) := by
  rw [zpow_add₀ ha]
  exact h

/-! ### R16. `two_ne_zero` · closes `(2 : α) ≠ 0`; the usual argument of R15 for powers of 2 -/
example : (2 : ℝ) ≠ 0 := two_ne_zero

/-! ### R17. `zpow_one` · `a ^ (1 : ℤ) = a` · goal -/
example {α : Type} [GroupWithZero α] (a : α) (P : α → Prop) (h : P a) : P (a ^ (1 : ℤ)) := by
  rw [zpow_one]
  exact h

/-! ### R18. `calc` · closes `a ≤ d` from a chain `a ≤ b = c ≤ d`, one justification per link
`_` on the first line stands for the left side of the goal. -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b = c) (h3 : c ≤ d) : a ≤ d := by
  calc _ ≤ b := h1
    _ = c := h2
    _ ≤ d := h3

/-! ### R19. `gcongr` · goal `c * a ≤ c * b` → goal `a ≤ b` (it proves `0 ≤ c` itself)
If `a ≤ b` is already a hypothesis, `gcongr` closes the goal outright. -/
example (a b : ℝ) (k : ℤ) (h : b - a ≥ 0) : 2 ^ k * a ≤ 2 ^ k * b := by
  gcongr
  linarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A relative-error witness: `y = x * (1 + δ)` with `δ := (y - x) / x` (R2, then `ring`) -/
example (x y : ℝ) (hx : 0 < x) : y = x * (1 + (y - x) / x) := by
  field_simp
  ring

/-! ### W2. Splitting an integer exponent (R14, R15 with R16, R17), then numbers -/
example (k : ℤ) : (2 : ℝ) ^ (k + 1) / 4 = 2 ^ (k - 1) := by
  rw [show k + 1 = (k - 1) + 1 + 1 by ring]
  rw [zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_one]
  ring

/-! ### W3. Bounding a quotient by a power of 2 (R12, R5, R13, then R18 with R19) -/
example (k : ℤ) (x r : ℝ) (hx : 0 < x) (hk : 2 ^ k ≤ x) (hr : |r| ≤ 2 ^ k / 4) :
    |r / x| ≤ 1 / 4 := by
  rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
  calc _ ≤ (2 : ℝ) ^ k / 4 := hr
    _ = 1 / 4 * 2 ^ k := by ring
    _ ≤ 1 / 4 * x := by gcongr

end M103Guide

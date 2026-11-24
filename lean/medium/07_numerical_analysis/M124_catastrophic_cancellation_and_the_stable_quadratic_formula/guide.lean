/- Guide for M124 (Catastrophic cancellation and the stable quadratic formula).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M124Guide

/-! # Part R · Reference entries -/

/-! ## Denominators and the triangle inequality (`sub_rel_error`) -/

/-! ### R1. `sub_ne_zero` · `a - b ≠ 0 ↔ a ≠ b` · goal: `a - b ≠ 0` → `a ≠ b`
As a term: `sub_ne_zero.mpr h : a - b ≠ 0` from `h : a ≠ b` (`.mpr` uses an `↔` right to left). -/
example {α : Type} [AddGroup α] (a b : α) (h : a ≠ b) : a - b ≠ 0 := by
  rw [sub_ne_zero]
  exact h

/-! ### R2. `abs_pos` · `0 < |a| ↔ a ≠ 0` · goal: `0 < |a|` → `a ≠ 0` -/
example (a : ℝ) (h : a ≠ 0) : 0 < |a| := by
  rw [abs_pos]
  exact h

/-! ### R3. `gcongr` on a common denominator · goal: `a / c ≤ b / c` → `a ≤ b`
The side goal `0 ≤ c` is proved by `gcongr` itself (here `c = |d|`, nonnegative by `positivity`). -/
example (a b d : ℝ) (h : a ≤ b ∧ True) : a / |d| ≤ b / |d| := by
  gcongr
  exact h.1

/-! ### R4. `rw [show e₁ = e₂ by ring]` · goal: `e₁` → a ring-equal `e₂` you choose -/
example (x d : ℝ) (P : ℝ → Prop) (h : P (x * d)) : P (x * (1 + d) - x) := by
  rw [show x * (1 + d) - x = x * d by ring]
  exact h

/-! ### R5. `calc` · goal list: `a ≤ c` → one goal per step (`?_` leaves a step open) -/
example (a b c : ℝ) (hab : a ≤ b) (hbc : b = c) : a ≤ c := by
  calc a ≤ b := ?_
    _ = c := ?_
  exact hab
  exact hbc

/-! ### R6. `abs_sub` · `|a - b| ≤ |a| + |b|` · goal, as a `calc` step: `|a - b| ≤ c` → `|a| + |b| ≤ c`
The name and statement are this Mathlib version's: check with `#check abs_sub`. -/
example (a b c : ℝ) (h : |a| + |b| ≤ c) : |a - b| ≤ c := by
  calc |a - b| ≤ |a| + |b| := abs_sub _ _
    _ ≤ c := ?_
  exact h

/-! ### R7. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R8. `gcongr` on a monotone expression · goal → the inequalities between the parts that differ
It closes those goals by `assumption` when the hypotheses are in context; here they are hidden in `h`. -/
example (a c p q u : ℝ) (h : p ≤ u ∧ q ≤ u) : |a| * p + |c| * q ≤ |a| * u + |c| * u := by
  gcongr
  exacts [h.1, h.2]

/-! ## Absolute values of known sign (`sub_rel_error_sharp`) -/

/-! ### R9. `abs_of_nonneg` · `0 ≤ a → |a| = a` · goal: `|a|` → `a` -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_nonneg ha]
  exact h

/-! ### R10. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · goal list: one goal per factor -/
example (a b : ℝ) (h : 0 ≤ a ∧ 0 ≤ b) : 0 ≤ a * b := by
  apply mul_nonneg
  exacts [h.1, h.2]

/-! ### R11. `linarith` · closes a linear `<`, `≤`, `=` or `≠` goal from hypotheses in context -/
example (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q) : p + q ≠ 0 := by
  linarith

/-! ### R12. `abs_of_pos` · `0 < a → |a| = a` · goal: `|a|` → `a` -/
example (a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ## `let`, square roots and clearing denominators (`stable_quadratic`) -/

/-! ### R13. `intro x` on a `let` goal · context gains `x : ℝ := e`; goal mentions `x` -/
example (e : ℝ) (P : ℝ → Prop) (h : P e) : let x := e; P x := by
  intro x
  exact h

/-! ### R14. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · context gains `hs : √d ^ 2 = d` -/
example (d : ℝ) (hd : 0 ≤ d) (G : Prop) (g : √d ^ 2 = d → G) : G := by
  have hs := Real.sq_sqrt hd
  exact g hs

/-! ### R15. `Real.sqrt_nonneg` · `0 ≤ √x` (no hypothesis needed) · context gains `hn : 0 ≤ √d` -/
example (d : ℝ) (G : Prop) (g : 0 ≤ √d → G) : G := by
  have hn := Real.sqrt_nonneg d
  exact g hn

/-! ### R16. `simp only [x]` for a `let` variable · goal: `x` → its value `e` (R13 shows it) -/
example (e : ℝ) (P : ℝ → Prop) (h : P e) : let x := e; P x := by
  intro x
  simp only [x]
  exact h

/-! ### R17. `generalize e = s at hs ⊢` · context and goal: every `e` → a fresh variable `s` -/
example (d : ℝ) (P : ℝ → Prop) (hs : √d ^ 2 = d) (h : ∀ s : ℝ, s ^ 2 = d → P (s + 1)) :
    P (√d + 1) := by
  generalize √d = s at hs ⊢
  exact h s hs

/-! ### R18. `field_simp` · goal: an equation with denominators → one without
It needs each denominator `≠ 0` in context (or provable by `simp`), and it reorders products. -/
example (x y z a : ℝ) (ha : a ≠ 0) (h : x + y * a = z * a) : x / a + y = z := by
  field_simp
  linear_combination h

/-! ### R19. `linear_combination k * h` · closes `L = R` when `L - R - k * (hl - hr)` is `0` by `ring`
(`h : hl = hr`; `k` may be any expression, and `k₁ * h₁ + k₂ * h₂` combines several facts). -/
example (p q k : ℝ) (h : p ^ 2 = q) : k * p ^ 2 + 1 = k * q + 1 := by
  linear_combination k * h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Known signs: R10 with R11 inside the arguments, then R9, R12; `rw` closes by `rfl`
`(by linarith : 0 < p)` proves the argument and says which fact it is. -/
example (p q u : ℝ) (hu : 0 ≤ u) (hq : 0 < q) (hqp : q < p) :
    |u * (p - q)| = u * (|p| - |q|) := by
  rw [abs_of_nonneg (mul_nonneg hu (by linarith)), abs_of_pos hq, abs_of_pos (by linarith : 0 < p)]

/-! ### W2. A `calc` chain: R6, then R7, then R8 -/
example (p q a u : ℝ) (ha : |a| ≤ u) : |p * a - q| ≤ |p| * u + |q| := by
  calc |p * a - q| ≤ |p * a| + |q| := abs_sub _ _
    _ = |p| * |a| + |q| := by rw [abs_mul]
    _ ≤ |p| * u + |q| := by gcongr

/-! ### W3. `let` + square root: R13, R14, R16, R17, R18, R19 -/
example (a d p : ℝ) (ha : a ≠ 0) (hd : 0 ≤ d) :
    let r := (√d - p) / a; a * r ^ 2 + 2 * p * r = (d - p ^ 2) / a := by
  intro r
  have hs := Real.sq_sqrt hd
  simp only [r]
  generalize √d = s at hs ⊢
  field_simp
  linear_combination hs

end M124Guide

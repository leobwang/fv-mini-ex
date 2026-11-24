/- Guide for E044 (gcongr).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`gcongr` closes every goal it can from the hypotheses in context (R3). So that an entry can SHOW the
goals `gcongr` produces, its hypothesis is packed into a conjunction `h : A ∧ B`, which `gcongr` does
not look inside; `exact h.1` / `exacts [h.1, h.2]` then finishes the example.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `exact`, `exacts`, `∧` and `.1`/`.2`, `<;>`.
-/
import Mathlib

namespace E044Guide

/-! # Part R · Reference entries -/

/-! ## What `gcongr` does to the goal
`gcongr` ("generalized congruence") works on a goal `lhs ≤ rhs` or `lhs < rhs` whose two sides have
the same shape and differ only in some positions. It peels the common shape off, one layer at a
time, using monotonicity lemmas Mathlib tags `@[gcongr]`, and leaves one goal per differing
position (a *main goal*) plus the conditions those lemmas need (*side goals*, such as `0 ≤ a`). -/

/-! ### R1. `gcongr` on `a + c ≤ b + c` · goal → `a ≤ b`
The shared summand `c` is dropped (on either side of `+`). -/
example (a b c : ℝ) (h : a ≤ b ∧ 0 ≤ c) : a + c ≤ b + c := by
  gcongr
  exact h.1

example (a b c : ℝ) (h : a ≤ b ∧ 0 ≤ c) : c + a ≤ c + b := by
  gcongr
  exact h.1

/-! ### R2. `gcongr` on `a ^ n ≤ b ^ n` · goal list → side goal `0 ≤ a`, main goal `a ≤ b`
`x ↦ x ^ n` is monotone only on `0 ≤ x` (`(-2) ^ 2 > 1 ^ 2`), hence the side goal. -/
example (a b : ℝ) (n : ℕ) (h : 0 ≤ a ∧ a ≤ b) : a ^ n ≤ b ^ n := by
  gcongr
  exacts [h.1, h.2]

/-! ### R3. `gcongr` closes main and side goals from the context · goal → no goals
Each goal `gcongr` produces is tried against the hypotheses; `h : a < b` also proves `a ≤ b`.
Only the goals no hypothesis proves are left to you. -/
example (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (h : a < b) : a ^ n ≤ b ^ n := by
  gcongr

/-! ### R4. `gcongr` on `a * c ≤ b * d` in `ℕ` · goal list → `a ≤ b`, `c ≤ d`
Two differing positions, two main goals. In `ℕ` every number is `≥ 0`, so the side goals that
multiplication needs (`0 ≤ c`, `0 ≤ b`) are closed automatically. In `ℝ` they are not (W2). -/
example (a b c d : ℕ) (h : a ≤ b ∧ c ≤ d) : a * c ≤ b * d := by
  gcongr
  exacts [h.1, h.2]

/-! ### R5. `gcongr` on `k / y < k / x` · goal list → `0 < k`, `0 < x`, and `x < y` (flipped)
`t ↦ k / t` is DEcreasing on `t > 0` when `k > 0`, so the main goal compares the denominators the
other way round: `x < y`. Side goals: the numerator is positive, the smaller denominator is positive. -/
example (k x y : ℝ) (h : 0 < k ∧ 0 < x ∧ x < y) : k / y < k / x := by
  gcongr
  exacts [h.1, h.2.1, h.2.2]

/-! ### R6. `positivity` · closes `0 < e` or `0 ≤ e` from the shape of `e`
Numerals, squares, sums and products of positive things. It does not read hypotheses, so it fails on
`0 < x` for a variable `x`. `gcongr` runs it on every side goal: that is why `0 < 2` never shows up. -/
example : (0 : ℝ) < 2 := by
  positivity

example (x : ℝ) : 0 < x ^ 2 + 1 := by
  positivity

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1, then multiplication by the constant `2` (side goal `0 ≤ 2` by R6), then R3 -/
example (x y : ℝ) (h : x ≤ y) : 2 * x + 1 ≤ 2 * y + 1 := by
  gcongr

/-! ### W2. A product in `ℝ`: unlike R4, the side goals `0 ≤ c` and `0 ≤ b` stay -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) (h : 0 ≤ b ∧ 0 ≤ c) : a * c ≤ b * d := by
  gcongr
  exacts [h.2, h.1]

/-! ### W3. Strict goal: the differing position must be strict too
From `h : x < y` this closes; from `x ≤ y` alone `gcongr` would leave `x < y` open. -/
example (x y : ℝ) (h : x < y) : 2 * x + 1 < 2 * y + 1 := by
  gcongr

/-! ### W4. R5 with a numeral numerator: R6 removes `0 < 1`, R3 the rest -/
example (x y : ℝ) (hx : 0 < x) (h : x < y) : 1 / y < 1 / x := by
  gcongr

end E044Guide

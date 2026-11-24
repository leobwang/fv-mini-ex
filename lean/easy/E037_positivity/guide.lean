/- Guide for E037 (positivity).
Part R: one reference entry per kind of expression `positivity` has to see through in the exercise,
each on a statement of the same shape as one hole but with other expressions. Put the cursor before
and after the step to see the proof state change in the infoview.
Part W: worked combinations on statements that are NOT the exercise's: the other goal forms
(`0 ≤ e`, `e ≠ 0`), division, and the same proof done by hand with the lemmas `positivity` uses.
Assumed: E001–E033 (tactic mode, `apply`/`exact` from E003, `rw` from E009). New: `import Mathlib`,
the number types `ℕ ℝ`, `|x|`, `Real.exp`, and the tactic `positivity`.
-/
import Mathlib

namespace E037Guide

/-! # Part R · Reference entries -/

/-! ## `positivity` closes `0 < e`, `0 ≤ e` or `e ≠ 0` by the shape of `e` -/

/-! ### R1. `positivity` on a sum of even powers and a positive numeral (`ℝ`) · closes the goal
It reads `e` as a tree. `y ^ 4` and `y ^ 2` are even powers, so `≥ 0` for every `y`; `2 * y ^ 2` is
`> 0` times `≥ 0`, so `≥ 0`; `1 > 0`. A sum of terms `≥ 0` with at least one `> 0` is `> 0`. -/
example (y : ℝ) : 0 < y ^ 4 + 2 * y ^ 2 + 1 := by
  positivity

/-! ### R2. `positivity` with variables bounded by hypotheses · closes the goal
A variable is a leaf of the tree: `positivity` knows nothing about `a` unless the context says so.
It reads hypotheses `0 < a`, `0 ≤ b` (also a positive numeral below `a`, as in `1 < a`).
Here `b + 2 > 0` (`≥ 0` plus `> 0`) and `a > 0`, and a product of two terms `> 0` is `> 0`. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < (b + 2) * a := by
  positivity

/-! ### R3. `positivity` on `Real.exp` · closes the goal
`Real.exp x` is `eˣ`, defined for every real `x` and always `> 0`; `positivity` knows that whatever
`x` is. -/
example (x : ℝ) : 0 < 3 * Real.exp x := by
  positivity

/-! ### R4. `positivity` on `|x|` · closes the goal
`|x|` is the absolute value of `x`. It is only `≥ 0` (it is `0` at `x = 0`), so a strict goal needs
another summand that is `> 0`; here `y`, through `hy`. -/
example (x y : ℝ) (hy : 0 < y) : 0 < |x| + y := by
  positivity

/-! ### R5. `positivity` in `ℕ` · closes the goal
In `ℕ` every term is `≥ 0`, so a variable `n` needs no hypothesis for `0 ≤ n`. A power `3 ^ n` of
a positive base is `> 0` for every exponent `n`; `n + 1` is `≥ 0` plus `> 0`. -/
example (n : ℕ) : 0 < 3 ^ n * (n + 1) := by
  positivity

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. A non-strict goal `0 ≤ e`: every leaf only needs `≥ 0` -/
example (x : ℝ) : 0 ≤ x ^ 2 + |x| := by
  positivity

/-! ### W2. A goal `e ≠ 0`: `positivity` proves `0 < e`, which implies it -/
example (x : ℝ) : Real.exp x + x ^ 2 ≠ 0 := by
  positivity

/-! ### W3. Division: `a / b > 0` when `a > 0` and `b > 0` -/
example (a : ℝ) (ha : 0 < a) : 0 < a / (a + 1) := by
  positivity

/-! ### W4. The same kind of proof by hand: `apply` a sum lemma, then one lemma per leaf
`add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b` leaves two goals (cases `ha`, `hb`).
`Real.exp_pos x : 0 < Real.exp x` and `sq_nonneg y : 0 ≤ y ^ 2` close them. -/
example (y : ℝ) : 0 < Real.exp y + y ^ 2 := by
  apply add_pos_of_pos_of_nonneg
  · exact Real.exp_pos y
  · exact sq_nonneg y

end E037Guide

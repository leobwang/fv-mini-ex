/- Guide for E035 (linarith).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α]` is "any ordered field" (`ℚ`, `ℝ`).
`P` stands for "the rest of your goal"; a hypothesis `g` in an entry is only there to finish the
example and shows what the context became.
Part W: worked combinations on inequalities that are NOT the exercise's.
Assumed: E001–E033 (tactic mode, `have`, `exact`), E034 (`import Mathlib`, `ℕ ℤ ℚ ℝ`, `ring`).
New: the tactic `linarith` and the lemma `sq_nonneg`.
-/
import Mathlib

namespace E035Guide

/-! # Part R · Reference entries -/

/-! ## `linarith`: linear consequences of the hypotheses -/

/-! ### R1. `linarith` with an `=` goal · closes the goal from linear equations in the context
`linarith` reads every hypothesis of the form `s = t`, `s ≤ t`, `s < t` (also `≥`, `>`) by itself.
An `=` goal is proved as two goals `≤` and `≥`. Here `a = (7 - b) / 2` and `b = 3`. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α)
    (h1 : 2 * a + b = 7) (h2 : b = 3) : a = 2 := by
  linarith

/-! ### R2. `linarith` with a `<` goal · closes the goal from a chain of `<` and `≤`
It negates the goal (`a < c` becomes `c ≤ a`) and finds nonnegative coefficients cᵢ with
Σ cᵢ·(hypᵢ) giving `0 < 0`. One strict `<` in the chain makes the conclusion strict. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α)
    (h1 : a < b) (h2 : b ≤ c) : a < c := by
  linarith

/-! ### R3. `linarith` with numeral coefficients and `-` · closes the goal
Coefficients may be any numerals (also `/ 2`): `linarith` scales hypotheses by positive rationals.
Here 1·`h1` + 2·`h2` + (negated goal `3 * b ≤ a + b`) sums to `0 < 0`. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α)
    (h1 : 0 ≤ a) (h2 : a < b) : 0 < 3 * b - (a + b) := by
  linarith

/-! ## Nonlinear goals: add a square, then everything is linear in the monomials -/

/-! ### R4. `sq_nonneg` · `∀ a, 0 ≤ a ^ 2` · context gains `h : 0 ≤ (a - b) ^ 2`
The argument is explicit: pass the expression to be squared, any expression at all. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) (P : Prop)
    (g : 0 ≤ (a - b) ^ 2 → P) : P := by
  have h := sq_nonneg (a - b)
  exact g h

/-! ### R5. `linarith [t]` · closes the goal, with the fact proved by the term `t` added
`t` is a proof term (here `sq_nonneg c : 0 ≤ c ^ 2`), not a statement. The context is unchanged.
`c ^ 2` is a monomial, which `linarith` treats as one unknown. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b c : α)
    (h : a ≤ b) : a ≤ b + c ^ 2 := by
  linarith [sq_nonneg c]

/-! ### R6. `linarith` multiplies out products · closes the goal
Before the search it expands every product and power into a sum of monomials (`a ^ 2`, `a * b`,
`a`, `1`, with `a * b` and `b * a` the same monomial) and treats each monomial as one unknown.
Here `h` reads `0 ≤ a ^ 2 - 2 * a + 1`, and the goal is linear in the unknowns `a ^ 2` and `a`. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a : α)
    (h : 0 ≤ (a - 1) ^ 2) : 2 * a ≤ a ^ 2 + 1 := by
  linarith

/-! # Part W · Worked combinations (not the exercise's inequalities) -/

/-! ### W1. Find the square: compute `rhs - lhs` by hand and check it with `ring` (E034) -/
example (a b : ℝ) : (a ^ 2 + b ^ 2) - -(2 * a * b) = (a + b) ^ 2 := by
  ring

/-! ### W2. The square as a hint (R4 inside R5, expanded as in R6) -/
example (a b : ℝ) : -(2 * a * b) ≤ a ^ 2 + b ^ 2 := by
  linarith [sq_nonneg (a + b)]

/-! ### W3. The same proof with the square first put in the context (R4, then R6) -/
example (a b : ℝ) : -(2 * a * b) ≤ a ^ 2 + b ^ 2 := by
  have h := sq_nonneg (a + b)
  linarith

/-! ### W4. Hypotheses with several strict and non-strict steps, coefficients `/ 2` -/
example (x y z : ℝ) (h1 : x ≤ y / 2) (h2 : y < z) (h3 : 0 ≤ z) : x < z := by
  linarith

end E035Guide

/- Guide for E068 (nlinarith with hints).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal". A hypothesis `g` in an entry is only there to finish the
example; it shows what the context became.
Part W: worked combinations on inequalities that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `have`, `exact`, implicit arguments.
-/
import Mathlib

namespace E068Guide

/-! # Part R · Reference entries -/

/-! ## The engine: linear arithmetic over an ordered field -/

/-! ### R1. `linarith` · closes a goal that is a LINEAR consequence of the hypotheses
It negates the goal (`x ≤ 6` becomes `6 < x`), adds it to the hypotheses of the form `a ≤ b`,
`a < b`, `a = b`, and looks for nonnegative coefficients cᵢ with Σ cᵢ·(hypᵢ) giving `0 < 0`.
Here: 1·`h1` + 2·`h2` + 1·`(6 < x)`. Every nonlinear monomial (`x * y`, `x ^ 2`) is an opaque
unknown to it, so `x ^ 2` and `x` are unrelated. -/
example (x y : ℝ) (h1 : x ≤ 2 * y) (h2 : y ≤ 3) : x ≤ 6 := by
  linarith

/-! ### R2. `nlinarith` · closes a POLYNOMIAL goal by first multiplying pairs of facts
It negates the goal as R1 does, then adds the product of every pair of facts in its list
(hypotheses, the negated goal, hints from R6) and `0 ≤ e ^ 2` for each square `e ^ 2` it sees,
then runs `linarith` on the result,
after expanding every product into monomials. Here the products `hx * hxy : 0 ≤ x * (y - x)` and
`hxy * hxy : 0 ≤ (y - x) ^ 2` suffice: `y ^ 2 - x ^ 2 = (y - x) ^ 2 + 2 * x * (y - x)`. -/
example (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  nlinarith

/-! ## Proof terms that are inequalities (the hints) -/

/-! ### R3. `add_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a + b` · context gains `h : 0 ≤ u + v`
`a b` are implicit: Lean reads them off the two proofs you pass. -/
example (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (P : Prop) (g : 0 ≤ u + v → P) : P := by
  have h := add_nonneg hu hv
  exact g h

/-! ### R4. `sq_nonneg` · `∀ a, 0 ≤ a ^ 2` · context gains `h : 0 ≤ (u - v) ^ 2`
The argument `a` is explicit: pass the expression to be squared, any expression at all. -/
example (u v : ℝ) (P : Prop) (g : 0 ≤ (u - v) ^ 2 → P) : P := by
  have h := sq_nonneg (u - v)
  exact g h

/-! ### R5. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · context gains `h : 0 ≤ u * v`
Arguments are the two proofs; they may themselves be terms built with R3 and R4. -/
example (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (P : Prop) (g : 0 ≤ u * v → P) : P := by
  have h := mul_nonneg hu hv
  exact g h

/-! ## Feeding the hints -/

/-! ### R6. `nlinarith [t₁, …, tₙ]` · closes the goal, with the facts `tᵢ` added to its list
Each `tᵢ` is a proof term (R3–R5), not a statement. The hints join the pairwise products of R2.
Here `(a + b) ^ 2 - 4 * a * b = (a - b) ^ 2`, so the one hint `0 ≤ (a - b) ^ 2` is the whole proof. -/
example (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! # Part W · Worked combinations (not the exercise's inequalities) -/

/-! ### W1. Find the hint: write `rhs - lhs` and check your factorisation with `ring` -/
example (x y : ℝ) : x ^ 3 + x * y ^ 2 - 2 * x ^ 2 * y = x * (x - y) ^ 2 := by
  ring

/-! ### W2. A (nonnegative factor) × (square) hint: R4 inside R5, then R6
`y` may be negative: only the factor `x` needs a sign. -/
example (x y : ℝ) (hx : 0 ≤ x) : 2 * x ^ 2 * y ≤ x ^ 3 + x * y ^ 2 := by
  nlinarith [mul_nonneg hx (sq_nonneg (x - y))]

/-! ### W3. The nonnegative factor is a sum: R3 and R4 inside R5, then R6
`rhs - lhs = (u + v) * (z - 1) ^ 2`. -/
example (u v z : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 2 * z * (u + v) ≤ (u + v) * (z ^ 2 + 1) := by
  nlinarith [mul_nonneg (add_nonneg hu hv) (sq_nonneg (z - 1))]

/-! ### W4. A sum of squares: one R4 hint per square, then R6
`a ^ 2 + b ^ 2 + 2 - 2 * (a + b) = (a - 1) ^ 2 + (b - 1) ^ 2`. -/
example (a b : ℝ) : 2 * (a + b) ≤ a ^ 2 + b ^ 2 + 2 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]

/-! ### W5. The same hints may live in the context instead: `nlinarith` reads hypotheses too -/
example (a b : ℝ) : 2 * (a + b) ≤ a ^ 2 + b ^ 2 + 2 := by
  have h1 := sq_nonneg (a - 1)
  have h2 := sq_nonneg (b - 1)
  nlinarith

end E068Guide

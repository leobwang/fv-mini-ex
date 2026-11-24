/- Guide for M066 (Bernoulli's inequality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became, and
`g : T → G` only uses a new hypothesis `h : T` so that the example closes.
R1 uses `?_` for the two cases so that both show up in the infoview; in the exercise you may put the
tactics right after each `=>` instead.
Part W: worked combinations on inequalities that are NOT the exercise's.
Assumed: Lean basics (E001–E033: `induction` (E014), `omega` (E011), `simp`, `rw`, `have`).
-/
import Mathlib

namespace M066Guide

/-! # Part R · Reference entries -/

/-! ## Induction on `ℕ` -/

/-! ### R1. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: one goal → two goals
Case `zero`: `n` becomes `0`. Case `succ`: `n` becomes `n + 1` (Mathlib prints `Nat.succ n` this way),
and the context gains the induction hypothesis `ih`, the goal for `n`. Hypotheses that do not
mention `n` (such as `hx : -1 ≤ x`) stay in the context unchanged. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ## The `zero` cases (`simp` applies R2 and R3 by itself) -/

/-! ### R2. `pow_zero` · `a ^ 0 = 1` · goal: a zeroth power → `1` -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P 1) : P (a ^ 0) := by
  rw [pow_zero]
  exact h

/-! ### R3. `Nat.cast_zero` · `((0 : ℕ) : α) = 0` · goal: the cast of the natural `0` → the `0` of `α`
`↑0` is the natural number `0` cast into `α` (for us `ℝ`). -/
example {α : Type} [AddMonoidWithOne α] (P : α → Prop) (h : P 0) : P ((0 : ℕ) : α) := by
  rw [Nat.cast_zero]
  exact h

/-! ## The `succ` cases -/

/-! ### R4. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal: peel one factor off a power
Afterwards the goal contains `a ^ n`, the power that `ih` talks about. -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R5. `omega` · closes linear (in)equalities over `ℕ`/`ℤ` from the hypotheses
A non-linear piece such as `3 ^ k` is treated as one opaque number (an *atom*). -/
example (k : ℕ) (ih : k + 2 ≤ 3 ^ k) : k + 3 ≤ 3 ^ k * 3 := by
  omega

/-! ### R6. `linarith` · closes a linear (in)equality over an ordered field (`ℝ`, `ℚ`) from the hypotheses -/
example (c x : ℝ) (hx : -c ≤ x) : 0 ≤ c + x := by
  linarith

/-! ### R7. `mul_le_mul_of_nonneg_right` · `b ≤ c → 0 ≤ a → b * a ≤ c * a` · context gains the product
`have h := mul_le_mul_of_nonneg_right hbc ha` multiplies both sides of `hbc` on the right by `a`. -/
example {α : Type} [Semiring α] [PartialOrder α] [IsOrderedRing α] (a b c : α) (hbc : b ≤ c)
    (ha : 0 ≤ a) (G : Prop) (g : b * a ≤ c * a → G) : G := by
  have h := mul_le_mul_of_nonneg_right hbc ha
  exact g h

/-! ### R8. `push_cast` · goal: casts moved inward, `↑(n + 1)` → `↑n + 1`
It rewrites with `Nat.cast_add`, `Nat.cast_one`, `Nat.cast_mul`, … so that the cast sits on the
variable `n` alone, the same atom `↑n` that `ih` contains. -/
example {α : Type} [AddMonoidWithOne α] (n : ℕ) (P : α → Prop) (h : P ((n : α) + 1)) :
    P ((n + 1 : ℕ) : α) := by
  push_cast
  exact h

/-! ## Facts to hand to `nlinarith` -/

/-! ### R9. `Nat.cast_nonneg` · `0 ≤ (↑n : α)` · context gains `0 ≤ ↑n`
Write the type: `(Nat.cast_nonneg n : (0 : ℝ) ≤ n)`, otherwise Lean does not know which `α`. -/
example {α : Type} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : ℕ) (G : Prop)
    (g : (0 : α) ≤ n → G) : G := by
  have h := (Nat.cast_nonneg n : (0 : α) ≤ n)
  exact g h

/-! ### R10. `sq_nonneg` · `0 ≤ a ^ 2` · context gains `0 ≤ a ^ 2` -/
example {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (a : α) (G : Prop)
    (g : 0 ≤ a ^ 2 → G) : G := by
  have h := sq_nonneg a
  exact g h

/-! ### R11. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · context gains `0 ≤ a * b` -/
example {α : Type} [Semiring α] [PartialOrder α] [IsOrderedRing α] (a b : α) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (G : Prop) (g : 0 ≤ a * b → G) : G := by
  have h := mul_nonneg ha hb
  exact g h

/-! ### R12. `nlinarith [t₁, t₂]` · closes polynomial (in)equalities over `ℝ`
It multiplies out every product, then works like `linarith` with each monomial (`a * b ^ 2`, …) as an
atom; it also tries products of pairs of hypotheses. Facts `tᵢ` in the brackets are added first: give
it the non-negative terms it cannot guess. -/
example (a b : ℝ) (ha : 0 ≤ a) : a ≤ a + a * b ^ 2 := by
  nlinarith [mul_nonneg ha (sq_nonneg b)]

/-! # Part W · Worked combinations (not the exercise's inequalities) -/

/-! ### W1. R1, then `simp` (R2) in `zero`, R4 → R5 in `succ` -/
example (n : ℕ) : 1 ≤ 3 ^ n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · simp
  · rw [pow_succ]
    omega

/-! ### W2. R8, then R7 on a fact proved by R6, then R6 -/
example (n : ℕ) (y : ℝ) (hy : 0 ≤ y) : (n : ℝ) * y ≤ ((n + 1 : ℕ) : ℝ) * y + y := by
  push_cast
  have h1 : (n : ℝ) ≤ n + 1 := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hy
  linarith

/-! ### W3. The hint term for R12, built from R11 with R10 and R9 -/
example (y : ℝ) (m : ℕ) : 0 ≤ y ^ 2 * m := by
  have h := mul_nonneg (sq_nonneg y) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  exact h

end M066Guide

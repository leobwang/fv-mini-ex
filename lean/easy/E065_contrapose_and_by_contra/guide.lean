/- Guide for E065 (contrapose! and by_contra!).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
A hypothesis `g` or `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `exact`, `have`, `rw`, `∀`/`→` hypotheses applied to arguments,
`¬ p` meaning `p → False`, bounded quantifiers `∀ ε > 0, …` (E025).
-/
import Mathlib

namespace E065Guide

/-! # Part R · Reference entries -/

/-! ## Contrapositive: swap a hypothesis and the goal -/

/-! ### R1. `contrapose! h` on `≠` · context and goal: `h : a ≠ b ⊢ c ≠ d` → `h : c = d ⊢ a = b`
`contrapose! h` turns "from `h` prove the goal" into "from `¬ goal` prove `¬ h`", and names the new
hypothesis `h` again. The `!` then pushes each `¬` inward: `¬ (c ≠ d)` becomes `c = d`. -/
example {α : Type} (a b c d : α) (g : c = d → a = b) (h : a ≠ b) : c ≠ d := by
  contrapose! h
  exact g h

/-! ### R2. `ring` · closes an identity of commutative rings (here: a power of `0`) -/
example {R : Type} [CommRing R] (a : R) : (a - a) ^ 3 = 0 := by
  ring

/-! ### R3. `contrapose! h` on `<` · context and goal: `h : a < b ⊢ c < d` → `h : d ≤ c ⊢ b ≤ a`
In a linear order `¬ (x < y)` is pushed to `y ≤ x`: the sides swap. -/
example {α : Type} [LinearOrder α] (a b c d : α) (g : d ≤ c → b ≤ a) (h : a < b) : c < d := by
  contrapose! h
  exact g h

/-! ### R4. `exact g u v h` · closes the goal by applying a `∀ x y, Q x y → S x y` hypothesis
Arguments go in the order of the binders: first the two values, then the proof of `Q u v`. -/
example {α : Type} (Q S : α → α → Prop) (g : ∀ x y, Q x y → S x y) (u v : α) (h : Q u v) :
    S u v := by
  exact g u v h

/-! ## Contradiction: assume the negated goal, derive `False` -/

/-! ### R5. `by_contra! h` · context gains `h : ¬ goal` (pushed), goal becomes `False`
For the goal `a ≤ b`, the new hypothesis is `¬ (a ≤ b)` pushed to `b < a`. -/
example {α : Type} [LinearOrder α] (a b : α) (g : b < a → False) : a ≤ b := by
  by_contra! h
  exact g h

/-! ### R6. `have := h e he` · context gains `this : Q e` (the instance of a bounded `∀`)
`h : ∀ ε > z, Q ε` is `∀ ε, ε > z → Q ε`: give it the value `e` and a proof `he : e > z`.
Without a name, `have` calls the new fact `this`. -/
example {α : Type} [LT α] (z e : α) (Q : α → Prop) (h : ∀ ε > z, Q ε) (he : e > z) : Q e := by
  have := h e he
  exact this

/-! ### R7. `linarith` · closes a goal `t < 0`, `t ≤ 0`, `t = 0`, … that follows linearly from the context
Division by a numeral, `x / 3`, counts as `(1/3) * x`, so it is linear too. Typical use:
`(by linarith)` proves a side condition such as `x / 3 > 0` in place. -/
example (x : ℝ) (hx : 0 < x) : x / 3 > 0 := by
  linarith

/-! ### R8. `linarith` with goal `False` · closes it when the hypotheses are linearly contradictory -/
example (x y : ℝ) (h1 : x + y < 0) (h2 : 0 ≤ x) (h3 : 0 ≤ y) : False := by
  linarith

/-! ### R9. `lt_irrefl a : ¬ a < a` · closes `False` from a proof of `a < a`
`¬ p` is `p → False`, so `lt_irrefl a` applied to `h : a < a` is a proof of `False`. -/
example {α : Type} [Preorder α] (a : α) (h : a < a) : False := by
  exact lt_irrefl a h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1, then `rw [h]`, then R2 -/
example (x : ℝ) (h : 2 * x ≠ 0) : x ≠ 0 := by
  contrapose! h
  rw [h]
  ring

/-! ### W2. R5, R6 with `(by linarith)`, R8: a number below every positive number plus one -/
example (x : ℝ) (h : ∀ ε > 0, x < ε + 1) : x ≤ 1 := by
  by_contra! hx
  have := h (x - 1) (by linarith)
  linarith

/-! ### W3. R5, then R9 applied to an instance of the hypothesis -/
example (s : ℕ → ℕ) (a : ℕ) (h : ∀ c, s c < a → s c < s c) : a ≤ s 0 := by
  by_contra! h'
  exact lt_irrefl (s 0) (h 0 h')

end E065Guide

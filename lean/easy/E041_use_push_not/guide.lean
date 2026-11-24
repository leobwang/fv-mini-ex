/- Guide for E041 (use and push Not).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`P : α → Prop` stands for "the rest of your goal": the step changes only the part shown inside
`P (…)`. A hypothesis `h` in an entry is only there to finish the example; it shows what the goal
became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E033 (`intro` E003, `∃` and `⟨x, h⟩` E007, `¬` E008, `rw` E009, `omega` E011).
New: `import Mathlib`, the Mathlib tactics `push Not` and `use`, and the order type class
`LinearOrder`.
-/
import Mathlib

namespace E041Guide

/-! # Part R · Reference entries -/

/-! ## `push Not`: move a negation inward -/

/-! ### R1. `push Not` on `¬ ∀` · goal: `¬ ∀ x, P x` → `∃ x, ¬P x`
Mathlib lemma `not_forall : (¬ ∀ x, P x) ↔ ∃ x, ¬ P x` (classical logic). -/
example {α : Type} (P : α → Prop) (h : ∃ x, ¬ P x) : ¬ ∀ x, P x := by
  push Not
  exact h

/-! ### R2. `push Not` on `¬ (a < b)` · goal: `¬ (a < b)` → `b ≤ a`
Mathlib lemma `not_lt : ¬ a < b ↔ b ≤ a`, true in any `LinearOrder` (a total order: `ℕ ℤ ℚ ℝ`). -/
example {α : Type} [LinearOrder α] (a b : α) (h : b ≤ a) : ¬ a < b := by
  push Not
  exact h

/-! ### R3. `push Not` on `¬ (a ≤ b)` · goal: `¬ (a ≤ b)` → `b < a`
Mathlib lemma `not_le : ¬ a ≤ b ↔ b < a`, again in any `LinearOrder`. -/
example {α : Type} [LinearOrder α] (a b : α) (h : b < a) : ¬ a ≤ b := by
  push Not
  exact h

/-! ### R4. `push Not` on `¬ ∃` · goal: `¬ ∃ x, P x` → `∀ x, ¬P x`
Mathlib lemma `not_exists : (¬ ∃ x, P x) ↔ ∀ x, ¬ P x`. -/
example {α : Type} (P : α → Prop) (h : ∀ x, ¬ P x) : ¬ ∃ x, P x := by
  push Not
  exact h

/-! ### R5. `push Not` through nested quantifiers · goal: one call pushes `¬` all the way in
Each quantifier it passes flips (`∃ ↔ ∀`); the `¬` ends on the innermost statement, where R2/R3
apply if it is an order. -/
example {α β : Type} (Q : α → β → Prop) (h : ∀ x, ∃ y, ¬ Q x y) : ¬ ∃ x, ∀ y, Q x y := by
  push Not
  exact h

/-! ## `use`: give the witness of an `∃` -/

/-! ### R6. `use a` · goal: `∃ x, P x` → `P a`
Same as `refine ⟨a, ?_⟩` (E007), then `use` tries to close `P a` itself (R7). Here it cannot, so
`P a` is left. -/
example {α : Type} (P : α → Prop) (a : α) (h : ∀ x, P x) : ∃ x, P x := by
  use a
  exact h a

/-! ### R7. `use a` that closes the goal · goal list: `∃ x, a ≤ x` → no goals
After filling the witness, `use` runs `rfl` / `trivial` on what is left. `a ≤ a` is closed by `rfl`
(Mathlib registers `le_refl : a ≤ a` with `rfl`); `n * n = 16` on numerals by evaluation. A strict
`3 < 4` is NOT closed: follow with `norm_num` or `omega` (W1). -/
example {α : Type} [Preorder α] (a : α) : ∃ x, a ≤ x := by
  use a

example : ∃ n : ℕ, n * n = 16 := by
  use 4

/-! ### R8. `use a, b` · goal: `∃ x y, P x y` → `P a b`
One witness per `∃`, in order, separated by commas. -/
example {α : Type} (P : α → α → Prop) (a b : α) (h : ∀ x y, P x y) : ∃ x y, P x y := by
  use a, b
  exact h a b

/-! ### R9. `use a, b` on `∃ x y, A ∧ B` · goal list: closed when each conjunct is closed by `rfl`
`use` also splits the `∧` that follows the witnesses and tries `rfl` on each side. -/
example {α : Type} (a b : α) : ∃ x y, x = a ∧ y = b := by
  use a, b

/-! ## After the negation is pushed -/

/-! ### R10. `intro x` (E003) · goal `∀ x, P x` → context gains `x`, goal `P x` -/
example {α : Type} (P : α → Prop) (h : ∀ x, P x) : ∀ y, P y := by
  intro x
  exact h x

/-! ### R11. `rw [hf]` with `hf : ∀ n, f n = g n` · goal: `f t` → `g t`
`rw` picks `n := t` from the first `f _` it finds in the goal (E009 used `rw` with plain equations). -/
example (f g : ℕ → ℕ) (hf : ∀ n, f n = g n) (t : ℕ) (P : ℕ → Prop) (h : P (g t)) : P (f t) := by
  rw [hf]
  exact h

/-! ### R12. `omega` (E011) · closes a linear (in)equality over `ℕ` / `ℤ`
Multiplication by a numeral is linear; `m * m` is not. -/
example (m : ℕ) : m < 3 * (m + 1) := by
  omega

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1 + R3, then R6, then `norm_num`: `use` alone does not close `10 < 11` -/
example : ¬ ∀ x : ℤ, x ≤ 10 := by
  push Not
  use 11
  norm_num

/-! ### W2. R4 + R5 + R2, then R10, R6, R11, R12: "no bound `B` exceeds every `g n`" -/
example (g : ℕ → ℕ) (hg : ∀ n, g n = n + 3) : ¬ ∃ B, ∀ n, g n < B := by
  push Not
  intro B
  use B
  rw [hg]
  omega

/-! ### W3. R8 + R9 with numerals: `use` evaluates both conjuncts -/
example : ∃ a b : ℕ, a * b = 15 ∧ a + b = 8 := by
  use 3, 5

/-! ### W4. `push Not at h` · context: the same rewrites on a hypothesis
`¬ (a = b)` becomes `a ≠ b`. -/
example (g : ℕ → ℕ) (h : ¬ ∀ n, g n = 0) : ∃ n, g n ≠ 0 := by
  push Not at h
  exact h

end E041Guide

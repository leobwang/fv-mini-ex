/- Guide for E034 (ring).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`{α : Type}` is any type; a bracket such as `[CommRing α]` says what `α` must support (a type
class). `P : α → Prop` stands for "the rest of your goal": the step changes only the part shown
inside `P (…)`. A hypothesis `hP` in an entry is only there to finish the example.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E033 (tactic mode, `rw` from E009, the `rfl` pattern from E025/E030). New: `import
Mathlib`, the number types `ℕ ℤ ℚ ℝ`, and the tactics `ring` and `subst`.
-/
import Mathlib

namespace E034Guide

/-! # Part R · Reference entries -/

/-! ## `ring`: identities that follow from the ring axioms alone -/

/-! ### R1. `ring` in a commutative ring (`ℤ`, `ℚ`, `ℝ`) · closes the goal
`[CommRing α]`: `α` has `0 1 + - *` and `^` by a natural-number exponent, `*` is commutative, and
the usual laws hold. `ring` puts both sides in a normal form (a sum of monomials) and compares. -/
example {α : Type} [CommRing α] (a b : α) : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by
  ring

/-! ### R2. `ring` in a commutative semiring (`ℕ`) · closes the goal
`[CommSemiring α]`: like R1 but with no subtraction. `ℕ` is one; its `-` truncates at `0`, so it is
not a ring operation and `ring` cannot reason about it. -/
example {α : Type} [CommSemiring α] (n : α) : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by
  ring

/-! ## Using a hypothesis first (`ring` never reads the context) -/

/-! ### R3. `subst h` with `h : a = e` · context: the variable `a` and `h` disappear; `a` → `e` everywhere
`a` must be a local variable that does not occur in `e`. Works the same for `h : e = a`. It is the
tactic form of the `rfl` pattern (E025, E030). `[Add α]` only makes `b + c` well typed. -/
example {α : Type} [Add α] (a b c : α) (P : α → Prop) (hP : P (b + c)) (h : a = b + c) : P a := by
  subst h
  exact hP

/-! ### R4. `rw [h]` with `h : a = e` · goal: `a` → `e`; context unchanged (`h` stays)
The alternative to R3; also works when `a` is not a variable (E009). -/
example {α : Type} [Add α] (a b c : α) (P : α → Prop) (hP : P (b + c)) (h : a = b + c) : P a := by
  rw [h]
  exact hP

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. `subst`, then `ring` (R3, R1) over `ℤ` -/
example (x y : ℤ) (h : x = y + 1) : x ^ 2 = y ^ 2 + 2 * y + 1 := by
  subst h
  ring

/-! ### W2. `rw [h]` with a numeral, then `ring` (R4, R1) over `ℝ`: `ring` also evaluates numerals -/
example (x : ℝ) (h : x = 2) : x ^ 2 + x = 6 := by
  rw [h]
  ring

/-! ### W3. `ring` over `ℕ` and `ℚ` (R2, R1): the type changes nothing in the proof -/
example (n : ℕ) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  ring

example (x y : ℚ) : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by
  ring

end E034Guide

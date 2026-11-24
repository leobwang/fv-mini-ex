/- Guide for E088 (set and generalize).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `g` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `have`, `exact`, `rcases`, `omega`, `decide`, `<;>`.
-/
import Mathlib

namespace E088Guide

/-! # Part R · Reference entries -/

/-! ## Bounding a remainder, then naming it -/

/-! ### R1. `Nat.mod_lt` · `(x : ℕ) {y : ℕ} : 0 < y → x % y < y` · context gains `h : a % b < b`
The divisor `y` is implicit: Lean reads it off the proof of `y > 0`. For a numeral divisor, prove
that side fact inline: `Nat.mod_lt a (by omega : 5 > 0)`. -/
example (a b : ℕ) (hb : b > 0) (P : Prop) (g : a % b < b → P) : P := by
  have h := Nat.mod_lt a hb
  exact g h

example (a : ℕ) (P : Prop) (g : a % 5 < 5 → P) : P := by
  have h := Nat.mod_lt a (by omega : 5 > 0)
  exact g h

/-! ### R2. `generalize e = m at h ⊢` · goal and context: every `e` → a fresh variable `m`
`m` is a new, unconstrained `ℕ`: Lean forgets that it was `e`. Whatever you still need to know
about it must already sit in a hypothesis listed after `at` (here `h`); `⊢` names the goal. -/
example (a b : ℕ) (Q : ℕ → Prop) (h : a % b < b) (g : ∀ m, m < b → Q m) : Q (a % b) := by
  generalize a % b = m at h ⊢
  exact g m h

/-! ## Case split on a small variable -/

/-! ### R3. `omega` · closes a disjunction of values from a bound: `m < 3 → m = 0 ∨ m = 1 ∨ m = 2`
Inline, `(by omega : m = 0 ∨ m = 1)` is a proof term of that disjunction, ready for `rcases`. -/
example (m : ℕ) (h : m < 2) : m = 0 ∨ m = 1 := by
  omega

/-! ### R4. `rcases hm with rfl | rfl | rfl` · goal list: one goal per value, `m` replaced by it
The pattern `rfl` on `m = 0` substitutes `0` for `m` everywhere and drops the equation. This needs
`m` to be a variable: `n % 3 = 0` cannot be substituted (that is why R2 comes first). -/
example (P : ℕ → Prop) (m : ℕ) (hm : m = 0 ∨ m = 1 ∨ m = 2) (g0 : P 0) (g1 : P 1) (g2 : P 2) :
    P m := by
  rcases hm with rfl | rfl | rfl
  exacts [g0, g1, g2]

/-! ### R5. `decide` · closes a decidable statement about concrete numbers
It evaluates both sides. Any free variable (`m`, `n`) makes it fail, so substitute first (R4). -/
example : 2 * 2 % 5 ≠ 3 := by
  decide

/-! ## Abbreviating a term -/

/-! ### R6. `set y := e with hy` · context gains `y := e` and `hy : y = e`; every `e` → `y`
Unlike R2, `set` keeps the definition: `y` is a local definition (shown `y : ℝ := e`) and `hy`
records it. It replaces `e` in the goal and in every hypothesis. It only renames: what is
provable does not change. `ℝ` is Mathlib's real numbers; `a ^ 2` is the power with `2 : ℕ`. -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a ^ 2 + b)) : P (a ^ 2 + b) := by
  set y := a ^ 2 + b with hy
  exact h

/-! ### R7. `linarith` · closes a linear (in)equality over `ℝ`, `ℚ`, `ℤ`, `ℕ` from the hypotheses
Mathlib's `linarith` combines hypotheses linearly; a product with a numeral (`y * 3`) is linear.
A nonlinear piece such as `a ^ 2` is treated as one unknown atom. -/
example (y : ℝ) (h : y * 3 = 12) : y = 4 := by
  linarith

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1 → R2 → R3 → R4 → R5 on `n % 2`: squaring a remainder mod 2 changes nothing -/
example (n : ℕ) : (n % 2) * (n % 2) % 2 = n % 2 := by
  have h := Nat.mod_lt n (by omega : 2 > 0)
  generalize n % 2 = m at h ⊢
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> decide

/-! ### W2. R6 then R7: `linarith` sees `a ^ 2` as an atom, with or without the abbreviation -/
example (a : ℝ) (h : 3 * (a ^ 2 - 1) = 6) : a ^ 2 - 1 = 2 := by
  set t := a ^ 2 - 1 with ht
  linarith

example (a : ℝ) (h : 3 * (a ^ 2 - 1) = 6) : a ^ 2 - 1 = 2 := by
  linarith

end E088Guide

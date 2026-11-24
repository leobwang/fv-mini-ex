/- Guide for E063 (Casts).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`↑m` (written `(m : ℝ)` in source) is `Nat.cast m`, the natural number `m : ℕ` seen as a real number.
Part W: worked combinations on other cast expressions.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E063Guide

/-! # Part R · Reference entries -/

/-! ## Moving casts inward, then doing algebra in ℝ -/

/-! ### R1. `push_cast` · goal: `↑` pushed down to the variables and numerals
`↑((m + 1) * n)` (one cast of a ℕ product) becomes `(↑m + 1) * ↑n` (ℝ arithmetic on casts). -/
example (m n : ℕ) (P : ℝ → Prop) (h : P ((↑m + 1) * ↑n)) : P (((m + 1) * n : ℕ) : ℝ) := by
  push_cast
  exact h

/-! ### R2. `ring` · closes a commutative-ring identity in ℝ; each `↑m` counts as one unknown -/
example (m n : ℕ) : ((m : ℝ) + 1) * n = (m : ℝ) * n + n := by
  ring

/-! ## A ℕ fact seen through the cast -/

/-! ### R3. `exact_mod_cast h` · closes a ℕ goal from a hypothesis about the casts (ℝ → ℕ) -/
example (m n : ℕ) (h : (m : ℝ) + 1 ≤ (n : ℝ)) : m + 1 ≤ n := by
  exact_mod_cast h

/-! ### R4. `norm_cast at h` · context: `h` loses its casts (pulled outward, then dropped)
On the goal, plain `norm_cast` does the same to the goal. Here the goal is a separate `G`; when the
cleaned `h` is the goal itself, `norm_cast at h` closes it on its own, and `exact h` after it fails. -/
example (m n : ℕ) (G : Prop) (g : m + 1 ≤ n → G) (h : (m : ℝ) + 1 ≤ (n : ℝ)) : G := by
  norm_cast at h
  exact g h

/-! ### R5. `exact_mod_cast h` · closes a goal about casts from a ℕ hypothesis (ℕ → ℝ)
Numerals count as casts: `(1 : ℝ)` is read as `↑(1 : ℕ)`. -/
example (m n : ℕ) (h : m = n + 1) : (m : ℝ) = (n : ℝ) + 1 := by
  exact_mod_cast h

/-! ## Subtraction under the cast -/

/-! ### R6. `push_cast [hb]` · goal: `↑(a - b)` → `↑a - ↑b`, allowed by `hb : b ≤ a`
Without `hb`, `push_cast` leaves `↑(a - b)` alone: ℕ subtraction truncates at 0. -/
example (a b : ℕ) (hb : b ≤ a) (P : ℝ → Prop) (h : P ((a : ℝ) - (b : ℝ))) :
    P ((a - b : ℕ) : ℝ) := by
  push_cast [hb]
  exact h

/-! # Part W · Worked combinations (not the exercise's expressions) -/

/-! ### W1. Push, then algebra (R1, R2) -/
example (m n : ℕ) : ((m + n * m : ℕ) : ℝ) = (m : ℝ) * (1 + n) := by
  push_cast
  ring

/-! ### W2. A subtraction inside a sum (R6, R2) -/
example (a b c : ℕ) (hcb : c ≤ b) : ((a + (b - c) : ℕ) : ℝ) = a + b - c := by
  push_cast [hcb]
  ring

/-! ### W3. Numerals on the ℝ side (R5): `(3 : ℝ)` is matched with `(3 : ℕ)` -/
example (n : ℕ) (h : 3 < n) : (3 : ℝ) < (n : ℝ) := by
  exact_mod_cast h

/-! ### W4. Bring a real fact down to ℕ, then let `omega` (ℕ arithmetic) finish (R3) -/
example (n : ℕ) (h : (n : ℝ) + 2 < 1) : False := by
  have h' : n + 2 < 1 := by exact_mod_cast h
  omega

end E063Guide

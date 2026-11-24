/- Guide for E011 (omega).
Part R: one reference entry per kind of goal the exercise hands to `omega`, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`a b c : Nat` and `x y : Int` are arbitrary numbers; hypotheses `h`, `h1`, `h2` are the facts
`omega` reads from the context. Every entry is one step: `omega` closes the goal or fails.
Part W: worked combinations and limits, on statements that are NOT the exercise's.
Assumed: E001 (`decide`), E003 (tactic mode), E005 (`∧`, `constructor`), E009 (`rw`), E010 (`simp`).
-/

namespace E011Guide

/-! # Part R · Reference entries -/

/-! ## Linear arithmetic over `Nat` -/

/-! ### R1. `omega` · closes a linear goal over `Nat`, combining hypotheses from the context
Linear: built from variables, numerals, `+`, `-`, numeral `*` variable, `≤ < = ≥ >`. You never pass
the hypotheses: `omega` collects every arithmetic fact in the context by itself. -/
example (a b c : Nat) (h1 : a ≤ b) (h2 : b + 2 ≤ c) : a + 2 ≤ c := by
  omega

/-! ### R2. `omega` with `Nat` subtraction · closes the goal; uses `h : b ≤ a` to know `a - b` is exact
On `Nat`, `a - b` is `0` when `b > a` (truncated subtraction). `omega` splits on both cases itself;
the hypothesis `h` rules out the truncated case, without it this goal is false (`a = 0, b = 1`). -/
example (a b : Nat) (h : b ≤ a) : a - b + 2 * b = a + b := by
  omega

/-! ### R3. `omega` with truncation · closes `a - b = 0` when `a ≤ b` -/
example (a b : Nat) (h : a ≤ b) : a - b = 0 := by
  omega

/-! ## Systems over `Int`, connectives -/

/-! ### R4. `omega` on `Int` with `∧` in the goal · solves a linear system, both conjuncts at once
`Int` subtraction does not truncate; negative numbers exist. `omega` also handles `∨`, `¬`, `→`, `↔`
between linear facts, so there is no need to `constructor` first. -/
example (x y : Int) (h1 : x + y = 5) (h2 : x - y = 1) : x = 3 ∧ y = 2 := by
  omega

/-! ### R5. `omega` with casts `↑` (`Nat → Int`) · closes goals mixing `Nat` and `Int`
`((a : Nat) : Int)` prints as `↑a`. `omega` knows `↑a ≥ 0`, `↑(a + b) = ↑a + ↑b`, and that
`↑(a - b)` is the cast of a truncated difference (it splits on `b ≤ a` as in R2). -/
example (a b : Nat) (h : b ≤ a) : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
  omega

/-! ## Division and remainder by numerals -/

/-! ### R6. `omega` with `%` (and `/`) by a numeral · closes the goal
`a % 2` with a numeral divisor is linear: `omega` writes `a = 2 * q + r` with `0 ≤ r < 2`. A
variable divisor (`a % b`) is not. -/
example (a : Nat) (h : a % 2 = 1) : (a + 1) % 2 = 0 := by
  omega

/-! # Part W · Worked combinations and limits (not the exercise's statements) -/

/-! ### W1. Truncation computed: `decide` (E001) evaluates closed `Nat` and `Int` arithmetic -/
example : (3 : Nat) - 5 = 0 := by decide
example : (3 : Int) - 5 = -2 := by decide
example : (0 : Nat) - 1 + 1 = 1 := by decide

/-! ### W2. `omega` works over the integers: no integer solves `2 * x = 7`, so the goal `False` closes -/
example (x : Int) (h : 2 * x = 7) : False := by
  omega

/-! ### W3. `→`, `∀` and `∨` in the goal: `omega` introduces and splits by itself -/
example : ∀ n : Nat, n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  omega

/-! ### W4. A product of two variables is an opaque atom: `omega` treats `x * y` like one variable `t`
This works because only `t + 1 ≥ 4` from `t ≥ 3` is needed. A goal such as `x * y = y * x` or
`x * x ≥ 0` over `Int` needs facts about `*` itself, and `omega` fails on it. -/
example (x y : Nat) (h : x * y ≥ 3) : x * y + 1 ≥ 4 := by
  omega

/-! ### W5. `/` by a numeral, no hypothesis -/
example (a : Nat) : a / 2 ≤ a := by
  omega

end E011Guide

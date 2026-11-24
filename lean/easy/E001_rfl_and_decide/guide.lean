/- Guide for E001 (rfl, decide, #eval).
Part R: one reference entry per command, term or tactic the exercise needs. Put the cursor before and
after the step to see the proof state change in the infoview (the panel beside the editor).
`n a : Nat` are placeholders for any natural number; `f : Nat → Nat` is any function on them.
Part W: worked combinations on functions and numbers that are NOT the exercise's.
Assumed: nothing. This is the first Lean exercise.
-/

namespace E001Guide

/-! # Part R · Reference entries -/

/-! ## Definitions and evaluation -/

/-! ### R1. `def f (n : Nat) : Nat := e` · the environment gains a function `f : Nat → Nat`
`(n : Nat)` is the parameter and its type, `: Nat` after it is the result type, and the body `e` is an
expression of type `Nat` that may use `n`. Arithmetic on `Nat`: `+`, `*`, `^` (power), `-` (cut off at 0). -/
def triple (n : Nat) : Nat := 3 * n

/-! ### R2. `#eval e` · no proof state; the infoview prints the value of `e`
Application is written with a space: `triple 4`, not `triple(4)`. `#eval` only computes; it proves nothing. -/
#eval triple 4

/-! ## Statements and proofs -/

/-! ### R3. `example : P := proof` (or `theorem name : P := proof`) · the goal is the statement `P`
`P` is a proposition (a statement, type `Prop`); `proof` is a term of type `P`. `theorem` also names it.
Here `proof` is `rfl` (R4), which needs nothing. -/
example (a : Nat) : a = a := rfl

/-! ### R4. `rfl` (term) · closes `a = b` when both sides compute to the same value
Lean unfolds `triple` and evaluates `3 * 3`; both sides reach the numeral `9`. -/
example : triple 3 = 9 := rfl

/-! ### R5. `by tac` · switches to tactic mode: the infoview shows the goal `⊢ P`; `rfl` as a tactic
`(f : Nat → Nat) (a : Nat)`: an arbitrary function and number, so the goal is symbolic. -/
example (f : Nat → Nat) (a : Nat) : f a = f a := by
  rfl

/-! ### R6. `decide` · closes a decidable statement about concrete values (`<`, `≤`, `=`, `≠` on `Nat`)
Lean evaluates the statement to `true` and accepts that as a proof. `rfl` cannot prove `<`. -/
example : 3 ^ 3 < 30 := by
  decide

/-! ### R7. `&&`, `||`, `!` on `Bool`: `rfl` closes `b = true` when `b` computes to `true`
`Bool` has the two values `true`, `false`. `&&` is "and", `||` is "or", `!` is "not". A `Bool` is a value,
not a statement: `b = true` is the statement "`b` evaluates to `true`". Each operator computes by looking
at its first argument, so `true && b` reduces to `b` even for an unknown `b : Bool`. Write the parentheses
around the `Bool` side: `=` binds tighter than `&&`, `||` and `!`. -/
example (b : Bool) : (true && b) = b := by
  rfl

example : (!(false && true)) = true := by
  rfl

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. R1 then R2: define, then evaluate to check the definition -/
def square (n : Nat) : Nat := n * n
#eval square 7

/-! ### W2. One fact, three proofs: R4 as a term, R5 as a tactic, R6 (equality is decidable too) -/
example : square 4 = 16 := rfl
example : square 4 = 16 := by
  rfl
example : square 4 = 16 := by
  decide

/-! ### W3. R6 on a computed inequality: `decide` evaluates `square 5` too -/
example : square 5 ≤ triple 9 := by
  decide

/-! ### W4. R7 with `decide` instead of `rfl` -/
example : (true && !(true && false)) = true := by
  decide

end E001Guide

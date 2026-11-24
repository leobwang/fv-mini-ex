/- Guide for E002 (Factorial by pattern matching).
Part R: one reference entry per term or tactic the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`n k : Nat` are arbitrary natural numbers. A `def` body is a term; to show the goal such a term
closes, an entry feeds it to `exact` inside `by` (tactic mode, explained properly in E003: `by`
opens a proof state, `exact t` finishes the goal with the term `t`).
All entries use `tri` below (the triangular numbers `0 + 1 + ⋯ + n`), NOT the exercise's `fact`.
Part W: worked combinations on other functions (`pow2`, `len`).
Assumed: E001 (`def`, `theorem`/`example`, `rfl`, `decide`, `#eval`).
-/

namespace E002Guide

/-- Triangular numbers: `tri n = 0 + 1 + ⋯ + n`. Defined by `match` on `n` (R1). The second arm
calls `tri k` on the `k` inside `n = k + 1` (R2): structural recursion. -/
def tri (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => (k + 1) + tri k

/-! # Part R · Reference entries -/

/-! ## Defining a function on `Nat` by cases -/

/-! ### R1. `match n with | 0 => a | k + 1 => b` · closes a `⊢ Nat` goal, one arm per shape of `n`
Every `n : Nat` is either `0` or `k + 1` for some `k`, so these two arms cover all of `Nat`. The
pattern `k + 1` introduces the new name `k` (here: the predecessor). In a `def` body you write the
`match` directly after `:=`, as in `tri` above. This one is the predecessor function. -/
example (n : Nat) : Nat := by
  exact match n with
    | 0 => 0
    | k + 1 => k

/-! ### R2. Inside the arm `k + 1 => …` · context gains `k : Nat`; the value may call the function on `k`
`?_` leaves the arm's value unwritten and makes it a goal, only to show what that arm sees: `k`.
In `tri` itself the arm calls `tri k`. Lean accepts a call of the function being defined on `k`
(a part of the pattern `k + 1`, hence structurally smaller), and rejects `tri n` or `tri (n - 1)`. -/
example (n : Nat) : Nat := by
  refine match n with
    | 0 => 0
    | k + 1 => ?_
  exact (k + 1) + tri k

/-! ## Proving facts by computation -/

/-! ### R3. `rfl` on `f 0 = v` · closes the goal: `tri 0` unfolds to the `0` arm -/
example : tri 0 = 0 := by
  rfl

/-! ### R4. `rfl` on `f (n + 1) = …` with `n` a variable · closes the goal: one step of unfolding
`n + 1` has the shape of the pattern `k + 1` (with `k := n`), so `tri (n + 1)` unfolds to the second
arm's value even though `n` is unknown. The right side must be that value written the same way.
Lean prints `(n + 1) + tri n` as `n + 1 + tri n` (`+` groups to the left). -/
example (n : Nat) : tri (n + 1) = (n + 1) + tri n := by
  rfl

/-! ### R5. `rfl` (or `decide`) on `f 5 = v` · closes the goal: full evaluation
With a numeral argument Lean unfolds all the way down to `tri 0` and computes the numbers. -/
example : tri 5 = 15 := by
  rfl

/-! # Part W · Worked combinations (not the exercise's function) -/

/-! ### W1. Equation style: `def f : Nat → Nat | 0 => … | k + 1 => …` is the same `match`,
without naming the argument. `#eval` runs it: check the values before proving anything. -/
def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

#eval pow2 10

example : pow2 10 = 1024 := rfl

example (n : Nat) : pow2 (n + 1) = 2 * pow2 n := by
  rfl

/-! ### W2. Structural recursion on lists: the arm `_ :: xs` calls `len xs`, a part of the list -/
def len : List Nat → Nat
  | [] => 0
  | _ :: xs => 1 + len xs

example : len [7, 8, 9] = 3 := by
  decide

end E002Guide

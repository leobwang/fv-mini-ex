/- Guide for E012 (Absolute value).
Part R: one reference entry per term or tactic the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`c : Prop` is a condition, `[Decidable c]` says Lean can compute whether `c` holds (true for `x < 0`,
`x ≤ y`, `x = y` on `Int` and `Nat`). `P : α → Prop` stands for "the rest of your goal": the step
changes only the part shown inside `P (…)`. A hypothesis `h` in an entry is only there to finish
the example; it shows what the goal became.
Part W: worked combinations on other functions (`sgn`, `relu`), NOT the exercise's `myAbs`.
Assumed: E001 (`def`, `decide`, `#eval`), E002 (`exact` to show a `def` body), E003 (tactic mode),
E005 (`∧`, `∨`, `<;>`), E008 (`absurd`), E011 (`omega`).
-/

namespace E012Guide

/-- The sign of an integer, as `-1` or `1` (`0` counts as positive here). Defined by `if` (R1). -/
def sgn (x : Int) : Int := if x < 0 then -1 else 1

/-! # Part R · Reference entries -/

/-! ## Defining a function by cases on a condition -/

/-! ### R1. `if c then a else b` · closes a `⊢ α` goal: the value is `a` when `c` holds, else `b`
`c` must be decidable (`[Decidable c]`), so the program can test it at run time; `x < 0` on `Int`
is. Both branches have the same type `α`. In a `def` body write it directly after `:=`, as in `sgn`
above; here `exact` shows the goal such a term closes (as in E002). -/
example (c : Prop) [Decidable c] {α : Type} (a b : α) : α := by
  exact if c then a else b

/-! ## Proving facts about an `if` -/

/-! ### R2. `unfold f` · goal: every `f x` → the body of `f` with `x` substituted
After it the `if` is visible in the goal, so `split` (R3) can act on it. -/
example (x : Int) (P : Int → Prop) (h : P (if x < 0 then -1 else 1)) : P (sgn x) := by
  unfold sgn
  exact h

/-! ### R3. `split` · goal list: a goal containing `if c then a else b` → two goals
Goal `isTrue` has `a` in place of the `if` and gains `h✝ : c`; goal `isFalse` has `b` and gains
`h✝ : ¬c`. `h✝` is an inaccessible name: you cannot type it, but `omega`, `simp` and `‹c›` (the
anonymous hypothesis of type `c`) still use it. -/
example (c : Prop) [Decidable c] {α : Type} (a b : α) (P : α → Prop) (ha : c → P a)
    (hb : ¬c → P b) : P (if c then a else b) := by
  split
  exact ha ‹c›
  exact hb ‹¬c›

/-! ### R4. `omega` with a negated comparison and `∧`, `∨`, `-` in the goal · closes the goal
`¬x < y` is linear for `omega` (it reads it as `y ≤ x`), unary minus `-x` on `Int` is linear, and
`∧`, `∨` between linear facts are in its fragment, so no `constructor` or `left`/`right` first. -/
example (x y : Int) (h : ¬x < y) : y ≤ x ∧ (x - y = 0 ∨ -(x - y) < 0) := by
  omega

/-! # Part W · Worked combinations (not the exercise's function) -/

/-! ### W1. Check a definition by running it: `#eval` and `decide` (E001) -/
#eval sgn (-3)

example : sgn (-3) = -1 ∧ sgn 0 = 1 := by decide

/-! ### W2. `split` replaces EVERY copy of the same `if` at once
`sgn x * sgn x` unfolds to two copies of `if x < 0 then -1 else 1`; one `split` gives the goals
`-1 * -1 = 1` and `1 * 1 = 1`, never the mixed `-1 * 1`. -/
example (x : Int) : sgn x * sgn x = 1 := by
  unfold sgn
  split <;> decide

/-! ### W3. The full chain R1 → R2 → R3 → R4 on `relu x = max x 0` -/
def relu (x : Int) : Int := if x < 0 then 0 else x

example (x : Int) : 0 ≤ relu x ∧ x ≤ relu x := by
  unfold relu
  split <;> omega

/-! ### W4. Naming the branch hypothesis: `next h => …` instead of `h✝`
Needed when a branch is closed by a term that mentions the hypothesis. `Int.not_le` (core) is
`¬a ≤ b ↔ b < a`; `.mpr h` turns `h : x < 0` into `¬0 ≤ x`, which contradicts `hx`. -/
example (x : Int) (hx : 0 ≤ x) : relu x = x := by
  unfold relu
  split
  next h => exact absurd hx (Int.not_le.mpr h)
  next => rfl

end E012Guide

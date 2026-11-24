/- Guide for E026 (termination_by).
Part R: one reference entry per tactic, clause or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `k` in an entry is only there to finish the example; it shows what the goal became.
All entries use the guide's function `cd` below, NOT the exercise's.
Part W: worked combinations on `cd` and `digits`.
Assumed: Lean basics up to E025, in particular `def` and structural recursion by pattern matching
(E001, E002), `rw` (E009), `simp [f]` (E010), `omega` (E011), `if-then-else` (E012).
-/

namespace E026Guide

/-- Countdown: `cd 3 = [3, 2, 1]`. The recursive call is on `n - 1`, which is NOT a pattern variable
(as `k` is in `| k + 1 => …`), so structural recursion does not apply. `termination_by n` gives a
*measure*: a `Nat` that must get smaller at every recursive call (without the clause Lean tries to
guess one, and here it would succeed; the clause makes it explicit). Lean then proves `n - 1 < n` by
itself (R1), using the fact that the call sits in the `else` branch, where `¬n = 0` holds.
Lean generates the unfolding equation
  `cd.eq_1 : ∀ (n : Nat), cd n = if n = 0 then [] else n :: cd (n - 1)`
which `rw [cd]` and `simp [cd]` use. -/
def cd (n : Nat) : List Nat := if n = 0 then [] else n :: cd (n - 1)
termination_by n

/-! # Part R · Reference entries -/

/-! ## Writing a well-founded definition -/

/-! ### R1. `termination_by n` · the obligation it creates: `e < n` for each call `f e`
No goal is shown while you write the `def`: Lean creates this goal and closes it itself (with
`decreasing_tactic`, which tries `omega`). Its context holds the `if` condition of the branch the
call is in, under an inaccessible name `h✝`. If Lean cannot close it, the error
`failed to prove termination` shows this goal; then add `decreasing_by omega` after `termination_by`.
The example is the obligation for `cd`, with the hypothesis named `h`. -/
example (n : Nat) (h : ¬n = 0) : n - 1 < n := by
  omega

/-! ### R2. `omega` closes `n / 3 < n` · division by a numeral is fine
`n / 3` is `Nat` division, rounded down (`7 / 3 = 2`). `omega` understands `/` and `%` by a numeral
(not by a variable). A call `f (n / 3)` under `if n = 0 then … else …` gives exactly this
obligation. Without `h` it is false: `0 / 3 = 0`. -/
example (n : Nat) (h : ¬n = 0) : n / 3 < n := by
  omega

/-! ## Computing with it: closed goals -/

/-! ### R3. `simp [f]` · closes `f a = v` when `a` and `v` are numerals (literals)
`simp` rewrites `cd 3` with `cd.eq_1`, decides `3 = 0` to `False`, takes the `else` branch,
computes `3 - 1 = 2`, and repeats until no `cd` is left. It also splits an `∧` of such goals.
`rfl` and `decide` FAIL here: a well-founded definition does not compute by unfolding. -/
example : cd 3 = [3, 2, 1] := by
  simp [cd]

/-! ## Unfolding one step: goals with variables -/

/-! ### R4. `rw [f]` · goal: the first `f n` → its body, once
`rw [cd]` rewrites with `cd.eq_1`, instantiated at the FIRST `cd _` it finds; other calls such as
`cd (n - 1)` stay. With a variable `n` the `if` cannot be decided, so do not use `simp [cd]` here:
it keeps unfolding the new `cd (n - 1)` and fails with `maximum recursion depth has been reached`. -/
example (n : Nat) (P : List Nat → Prop) (k : P (if n = 0 then [] else n :: cd (n - 1))) :
    P (cd n) := by
  rw [cd]
  exact k

/-! ### R5. `if_neg : ¬c → (if c then t else e) = e` · goal: take the `else` branch
`rw [if_neg hc]` needs a proof `hc : ¬c` of the negated condition. The `then` twin is
`if_pos : c → (if c then t else e) = t`. -/
example {α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop) (hc : ¬c) (k : P e) :
    P (if c then t else e) := by
  rw [if_neg hc]
  exact k

/-! ### R6. `omega` closes `¬n ≤ k` from `h : k + 1 ≤ n` · use it as the argument `(by omega)`
In `rw [if_neg (by omega)]`, Lean first matches `if_neg` against the `if` in the goal, which fixes
`c`; then `omega` proves `¬c` from the hypotheses in context. -/
example (n k : Nat) (h : k + 1 ≤ n) : ¬n ≤ k := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- How many times `n` can be divided by 10 before it is below 10: `digits 345 = 2`. -/
def digits (n : Nat) : Nat := if n < 10 then 0 else 1 + digits (n / 10)
termination_by n

/-! ### W1. `simp [f]` iterates: 345 → 34 → 3, adding `1` at each step (R3) -/
example : digits 345 = 2 := by
  simp [digits]

/-! ### W2. One step on a variable: `rw [f]`, then `if_neg (by omega)` (R4, R5, R6)
After the second `rw` both sides are identical, so `rw` closes the goal itself (E009). -/
example (n : Nat) (h : 0 < n) : cd n = n :: cd (n - 1) := by
  rw [cd]
  rw [if_neg (by omega)]

end E026Guide

/- Guide for E094 (interval_cases).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`P`, `Q` stand for "the rest of your goal / hypothesis": the step changes only what sits inside `P (…)`.
A hypothesis `g` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033), in particular the hand-made case split of E031
(`have : n = 0 ∨ n = 1 := by omega; rcases this with rfl | rfl`).
-/
import Mathlib

namespace E094Guide

/-! # Part R · Reference entries -/

/-! ## Splitting a bounded variable into its values -/

/-! ### R1. `interval_cases n` on `ℕ` with two bounds · goal list: one goal per value
It reads a lower bound (`c ≤ n` or `c < n`) and an upper bound (`n ≤ d` or `n < d`) on `n` from the
context, and makes one goal for every value in between. In each goal `n` is replaced by the literal
in the goal AND in every hypothesis (`hq : Q n` becomes `hq : Q 1`); `n` itself stays in the context,
unused. The goals are named `case «1»`, `case «2»`, … after the value. -/
example (P Q : ℕ → Prop) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 3) (hq : Q n)
    (g : ∀ k, Q k → P k) : P n := by
  interval_cases n
  all_goals exact g _ hq

/-! ### R2. `t <;> u` after `interval_cases` · goal list: `u` runs on every goal `t` produced
One line finishes all branches when the same tactic closes each of them. -/
example (P Q : ℕ → Prop) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 3) (hq : Q n)
    (g : ∀ k, Q k → P k) : P n := by
  interval_cases n <;> exact g _ hq

/-! ## Closing one concrete branch -/

/-! ### R3. `simp_all` with a false hypothesis · closes the goal, whatever it is
`simp_all` simplifies every hypothesis and the goal with each other. A hypothesis that evaluates to
`False` (here `3 ^ 2 = 16`, i.e. `9 = 16`) proves any goal `G`. -/
example (G : Prop) (h : 3 ^ 2 = 16) : G := by
  simp_all

-- The same in `ℤ`: `2 ^ 3 - 2 = 0` evaluates to `6 = 0`, which is `False`.
example (G : Prop) (h : (2 : ℤ) ^ 3 - 2 = 0) : G := by
  simp_all

/-! ### R4. `simp_all` on a goal that is true once evaluated · closes the goal
Literal equations such as `0 = -1` evaluate to `False`, `0 = 0` to `True`, and the disjunction
`False ∨ True ∨ False` to `True`. True hypotheses such as `1 ≤ 3` are simplified away. -/
example : (0 : ℤ) = -1 ∨ (0 : ℤ) = 0 ∨ (0 : ℤ) = 1 := by
  simp_all

/-! ### R5. `interval_cases n` on `ℕ` with only an upper bound · goal list
On `ℕ` the lower bound `0 ≤ n` is built in, so `h : n < 3` alone gives the values `0, 1, 2`. -/
example (P : ℕ → Prop) (n : ℕ) (h : n < 3) (g0 : P 0) (g1 : P 1) (g2 : P 2) : P n := by
  interval_cases n
  exacts [g0, g1, g2]

/-! ### R6. `norm_num` · closes a numeric (in)equality between literals: `^`, `*`, `+`, `-`, `<`, `≤`, `≠` -/
example : 2 ^ 3 < 30 := by
  norm_num

/-! ### R7. `interval_cases x` on `ℤ` · goal list: needs BOTH bounds in the context
`ℤ` has no smallest element, so without a hypothesis like `-1 ≤ x` it fails with
"could not find lower bound on x". Negative values print as `-1`, goals as `case «-1»`. -/
example (P : ℤ → Prop) (x : ℤ) (h1 : -1 ≤ x) (h2 : x < 2) (gm : P (-1)) (g0 : P 0) (g1 : P 1) :
    P x := by
  interval_cases x
  exacts [gm, g0, g1]

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. ℕ, two bounds, only the goal is concrete: R1, then R6 on each branch -/
example (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 3) : n * n ≤ 9 := by
  interval_cases n
  all_goals norm_num

/-! ### W2. ℤ, a hypothesis kills a branch: R7, then R3 / R4 on each branch -/
example (x : ℤ) (h1 : -1 ≤ x) (h2 : x < 2) (h : x * x = 1) : x ≠ 0 := by
  interval_cases x
  all_goals simp_all

/-! ### W3. The bound is not of the form `n < d`: derive it first with `omega`, then split -/
example (n : ℕ) (h : 2 * n < 7) : n ^ 2 ≠ 2 := by
  have hn : n < 4 := by omega
  interval_cases n <;> norm_num

end E094Guide

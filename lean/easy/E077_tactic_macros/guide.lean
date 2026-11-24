/- Guide for E077 (Tactic macros).
Part R: one reference entry per tactic or command the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`α : Type` is any type, `A B : Prop` arbitrary propositions, `a b x y : Nat` arbitrary numbers,
`xs : List α` an arbitrary list. Hypotheses `h`, `hab` are the facts a closing tactic reads.
R1–R3 are the three closers, R4 combines them, R5–R6 give the combination a name.
Part W: worked combinations on goals and macros that are NOT the exercise's.
Assumed: E001 (`decide`), E003 (tactic mode, `exact`, `assumption`), E005 (`∧`, `constructor`), E009 (`rfl`),
E010 (`simp`, `simp_all`), E011 (`omega`).
-/

namespace E077Guide

/-! # Part R · Reference entries -/

/-! ## The three closers -/

/-! ### R1. `rfl` · closes `l = r` when both sides compute to the same term; otherwise fails
`[] ++ xs` computes to `xs`, because `++` is defined by recursion on its first list. -/
example {α : Type} (xs : List α) : [] ++ xs = xs := by
  rfl

/-! ### R2. `omega` · closes a linear `Nat`/`Int` goal, reading hypotheses such as `h`; otherwise fails -/
example (x y : Nat) (h : x ≤ y) : x < y + 1 := by
  omega

/-! ### R3. `simp_all` · simplifies every hypothesis and the goal with each other; here it closes the goal
It splits `hab : A ∧ B` into `A` and `B`, rewrites them to `True` in the goal, and `True ∧ True` is `True`. -/
example (A B : Prop) (hab : A ∧ B) : B ∧ A := by
  simp_all

/-! ## Combining tactics -/

/-! ### R4. `first | t₁ | t₂ | t₃` · goal: runs the first alternative that does not fail
`rfl` fails on `x < y + 1` (it is not an equation), so `first` moves on and `omega` closes it.
A failed alternative leaves no trace: the goal is as before when the next one starts. -/
example (x y : Nat) (h : x ≤ y) : x < y + 1 := by
  first | rfl | omega

/-! ## Naming a tactic script -/

/-! ### R5. `macro "name" : tactic => `(tactic| tac)` · a new tactic `name`; running it runs `tac`
`(tactic| …)` is a *quotation*: the tactic syntax `tac`, not yet run. Each use of `close_eq` below is
replaced by `first | rfl | omega` before Lean runs it, so it changes the goal exactly as R4 does. -/
macro "close_eq" : tactic => `(tactic| first | rfl | omega)

example (x y : Nat) (h : x ≤ y) : x < y + 1 := by
  close_eq

/-! ### R6. `syntax` + `macro_rules` · the same, declared in two steps; several expansions allowed
`syntax "name" : tactic` makes `name` parse as a tactic. Each `macro_rules` adds one expansion. Lean
tries the most recent one first; if it fails, the one before it. Here `omega` fails on a list
equation and the earlier rule, `rfl`, closes it. -/
syntax "close_two" : tactic
macro_rules | `(tactic| close_two) => `(tactic| rfl)
macro_rules | `(tactic| close_two) => `(tactic| omega)

example {α : Type} (xs : List α) : [] ++ xs = xs := by
  close_two

/-! ### R7. Hygiene · context: a name written inside a quotation is fresh, shown as `h✝`
`intro h` inside the macro adds a hypothesis the goal can only reach anonymously: it prints as `h✝`
(inaccessible; `exact h` would fail). Tactics that search the context (`omega`, `assumption`,
`simp_all`) still use it. In the same way, the macro cannot refer to a hypothesis of the goal by name. -/
macro "intro_h" : tactic => `(tactic| intro h)

example (a : Nat) : a = 3 → a + 1 = 4 := by
  intro_h
  omega

/-! # Part W · Worked combinations (not the exercise's goals) -/

/-! ### W1. A macro with `<;>` inside: split, then close each piece from the context
A macro cannot name the goal's hypotheses (`ha`): names written in a quotation are *hygienic*, a
fresh `ha` that the goal does not have. `assumption` searches the context instead. -/
macro "split_close" : tactic => `(tactic| constructor <;> assumption)

example (A B : Prop) (ha : A) (hb : B) : B ∧ A := by
  split_close

/-! ### W2. One macro, three kinds of goal: each use runs a different alternative of `first`
`assumption` closes a goal that is a hypothesis, `decide` (E001) a closed decidable statement, `omega`
linear arithmetic. On each goal the alternatives before the one that closes it fail. -/
macro "close_any" : tactic => `(tactic| first | assumption | decide | omega)

example (B : Prop) (hb : B) : B := by
  close_any

example : 2 + 3 = 5 := by
  close_any

example (a b : Nat) (h : b = a + 2) : a < b := by
  close_any

/-! ### W3. A macro expanding to a sequence: `(tactic| (t₁; t₂))` runs `t₁`, then `t₂`
`intro h` moves the premise into the context (E003); `omega` then reads it. -/
macro "intro_omega" : tactic => `(tactic| (intro h; omega))

example (a : Nat) : a = 3 → a + 1 = 4 := by
  intro_omega

end E077Guide

/- Guide for E016 (Bool and Option cases).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on `orDouble` (defined below) and other `Bool` / `Option` facts, not on the
exercise's `getOr` or theorems.
Assumed: Lean basics up to E015 (`rfl`, `exact`, `simp`, `simp at h`, `simp [f]`, `omega`, `cases` on
`Or`, `induction`).
-/

namespace E016Guide

/-- `orDouble o` is twice the value inside `o`, or `0` when there is none. -/
def orDouble (o : Option Nat) : Nat :=
  match o with
  | some x => 2 * x
  | none => 0

/-! # Part R · Reference entries -/

/-! ## Bool: two constructors -/

/-! ### R1. `cases b` (`b : Bool`) · goal list: one goal → a `false` goal and a `true` goal
`b` leaves the context and is replaced by `false` in the first goal and by `true` in the second. -/
example (P : Bool → Prop) (h0 : P false) (h1 : P true) (b : Bool) : P b := by
  cases b
  exact h0
  exact h1

/-! ### R2. `rfl` · closes an equation between closed `Bool` terms: both sides compute
With no variables left, `&&`, `||` and `!` evaluate by their defining tables. -/
example : (!true && true) = false := by
  rfl

/-! ### R3. `t <;> s` · goal list: run `s` on every goal that `t` produces
`cases b <;> rfl` splits and closes both cases in one line. -/
example (b : Bool) : (b && b) = b := by
  cases b <;> rfl

/-! ## Option: `none` or `some x` -/

/-! ### R4. `cases o` (`o : Option α`) · goal list: a `none` goal and a `some` goal
In the `some` goal the context gains the value inside, named `val✝` (the `✝` means you cannot type
the name). To name it yourself: `cases o with | none => … | some x => …`. -/
example {α : Type} (P : Option α → Prop) (h0 : P none) (h1 : ∀ x, P (some x)) (o : Option α) :
    P o := by
  cases o
  exact h0
  exact h1 _

/-! ### R5. `simp [f]` · goal: `f` applied to a constructor → the right side of that `match` arm
`simp [orDouble]` rewrites `orDouble (some x)` to `2 * x` and `orDouble none` to `0`. On `orDouble o`
with `o` unknown it only exposes `match o with …`, which cannot pick an arm: split `o` first (R4). -/
example (x : Nat) (P : Nat → Prop) (h : P (2 * x)) : P (orDouble (some x)) := by
  simp [orDouble]
  exact h

/-! ### R6. `simp` · closes `a ≤ a + d` (`Nat.le_add_right`) and `0 + d` → `d` (`Nat.zero_add`) -/
example (a d : Nat) : a ≤ a + d ∧ d ≤ 0 + d := by
  simp

/-! ## Simplifying a hypothesis about `Option.map` -/

/-! ### R7. `Option.map_none` · `Option.map f none = none` · context: `h` rewritten -/
example {α β : Type} (f : α → β) (b : β) (P : Prop) (hP : none = some b → P)
    (h : Option.map f none = some b) : P := by
  rw [Option.map_none] at h
  exact hP h

/-! ### R8. `simp at h` with `h : none = some b` · goal list: the goal is closed
Different constructors are never equal, so `simp` turns `h` into `False`, and a `False` hypothesis
proves any goal. -/
example {β : Type} (b : β) (P : Prop) (h : none = some b) : P := by
  simp at h

/-! ### R9. `Option.map_some` · `Option.map f (some a) = some (f a)` · context: `h` rewritten -/
example {α β : Type} (f : α → β) (a : α) (b : β) (P : Prop) (hP : some (f a) = some b → P)
    (h : Option.map f (some a) = some b) : P := by
  rw [Option.map_some] at h
  exact hP h

/-! ### R10. `Option.some.injEq` · `(some a = some b) = (a = b)` · context or goal: drop `some`
`simp` uses it by itself, on hypotheses (`simp at h`) and on the goal. -/
example {α : Type} (a b : α) (P : Prop) (hP : a = b → P) (h : some a = some b) : P := by
  simp at h
  exact hP h

/-! ### R11. `simp at h` · context: `h : a + k = n` with numerals `k ≤ n` → `h : a = n - k` -/
example (a : Nat) (P : Prop) (hP : a = 5 → P) (h : a + 2 = 7) : P := by
  simp at h
  exact hP h

/-! ### R12. `simp_all` · simplifies every hypothesis and the goal, rewriting each with the others
Here it rewrites the goal with `h` and drops the `some`s (R10). After `cases`, it does R7–R11 to the
hypothesis and then uses the result on the goal, all in one step. -/
example {α β : Type} (f : α → β) (a : α) (b : β) (h : f a = b) : some (f a) = some b := by
  simp_all

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R1 + R2 through R3: a `Bool` identity by evaluating both cases -/
example (b : Bool) : (!(b && b)) = !b := by
  cases b <;> rfl

/-! ### W2. R4 + R5 through R3: split, then unfold the `match` in each case; R6-style `simp` finishes -/
example (o : Option Nat) : orDouble o % 2 = 0 := by
  cases o <;> simp [orDouble]

/-! ### W3. R4 + R12 through R3: a hypothesis about `Option.map`; `none` case fine, `some` case absurd
In the `some` case `simp_all` turns `h` into `False` (R9, then `some _ = none` is `False` as in R8). -/
example (o : Option Nat) (h : o.map (· + 2) = none) : o = none := by
  cases o <;> simp_all

end E016Guide

/- Guide for M018 (Count with a for loop).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`F`, `G` are placeholder functions standing for "a fold with start value `c`" and "the recursive
specification", so the induction entries show the shape of the proof without the exercise's objects.
Part W: a worked combination on another loop (the sum of a list).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M018Guide

/-! # Part R · Reference entries -/

/-! ## From a `for` loop to `List.foldl` -/

/-! ### R1. `simp [f]` on a `for` loop · goal: `Id.run do … for … ` → `List.foldl`
`simp?` shows the lemmas used: `List.forIn_pure_yield_eq_foldl` (a pure `for` loop over a list whose
body always continues is a left fold), `bind_pure`, `Id.run_pure`. The loop variable becomes the fold's
accumulator `b`, the loop element its second argument `a`, and the initial value its start value. -/
def stepLoop (g : Nat → Nat) (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + g x
  return s

example (g : Nat → Nat) (xs : List Nat) (P : Nat → Prop)
    (h : P (xs.foldl (fun b a => b + g a) 0)) : P (stepLoop g xs) := by
  simp [stepLoop]
  exact h

/-! ### R2. `List.foldl_nil` · `[].foldl f b = b` · goal: a fold over `[]` → its start value -/
example {α β : Type} (f : β → α → β) (b : β) (P : β → Prop) (h : P b) : P (List.foldl f b []) := by
  rw [List.foldl_nil]
  exact h

/-! ### R3. `List.foldl_cons` · `(a :: l).foldl f b = l.foldl f (f b a)` · goal
One step of the fold: the head `a` is absorbed into the accumulator, the start value changes. -/
example {α β : Type} (f : β → α → β) (b : β) (a : α) (l : List α) (P : β → Prop)
    (h : P (l.foldl f (f b a))) : P ((a :: l).foldl f b) := by
  rw [List.foldl_cons]
  exact h

/-! ## Induction with a changing accumulator -/

/-! ### R4. `induction xs generalizing c` · goal list: one goal per constructor; context: `ih` is `∀ c`
`generalizing c` takes `c` out of the context before the induction and puts it back in each case, so
the induction hypothesis holds for EVERY start value. Without it (second example) `ih` is only about
the fixed `c`, and R3 changes `c`, so `ih` no longer matches. With `induction xs generalizing c with
| nil => … | cons x xs ih => …` you name the head, the tail and the hypothesis yourself. -/
example (F : List Nat → Nat → Nat) (G : List Nat → Nat) (h : ∀ ys d, F ys d = d + G ys)
    (xs : List Nat) (c : Nat) : F xs c = c + G xs := by
  induction xs generalizing c
  all_goals exact h _ _

example (F : List Nat → Nat → Nat) (G : List Nat → Nat) (h : ∀ ys d, F ys d = d + G ys)
    (xs : List Nat) (c : Nat) : F xs c = c + G xs := by
  induction xs
  all_goals exact h _ _

/-! ### R5. `simp only [g]` on a recursive definition · goal: `g (x :: xs)` → the `cons` equation
For a `def` by pattern matching, `simp only [g]` uses its equations: `g []` → the `[]` case, and
`g (x :: xs)` → the `x :: xs` case, which still mentions `g xs`. It does not unfold `g xs` further. -/
def sumL : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumL xs

example (P : Nat → Prop) (h : P 0) : P (sumL []) := by
  simp only [sumL]
  exact h

example (x : Nat) (xs : List Nat) (P : Nat → Prop) (h : P (x + sumL xs)) :
    P (sumL (x :: xs)) := by
  simp only [sumL]
  exact h

/-! ### R6. `rw [ih]` with a `∀` equation · goal: Lean picks the value of the bound variable
`ih : ∀ c, F xs c = c + G xs` rewrites `F xs t` for whatever `t` it finds (here `t := c + a`).
The same works with a theorem you proved yourself, and with `simp only [ih]` / `simp [myLemma]`. -/
example (F : List Nat → Nat → Nat) (G : List Nat → Nat) (xs : List Nat) (c a : Nat)
    (ih : ∀ c, F xs c = c + G xs) (P : Nat → Prop) (h : P (c + a + G xs)) :
    P (F xs (c + a)) := by
  rw [ih]
  exact h

example (F : List Nat → Nat → Nat) (G : List Nat → Nat) (xs : List Nat)
    (hF : ∀ ys d, F ys d = d + G ys) : F xs 0 = G xs := by
  simp only [hF]
  simp

/-! ### R7. `omega` · closes linear arithmetic over `Nat` and `Int`
It proves goals built from `+`, `-`, numerals, `*` by a numeral, `=`, `<`, `≤`, `∧`, `∨`, `¬`. Any other
subterm, such as `f x` or `if p then 1 else 0`, is treated as an unknown number (an *atom*), so
reassociating sums of atoms is fine. -/
example (f : Nat → Nat) (x c n : Nat) : c + f x + n = c + (f x + n) := by
  omega

example (p : Prop) [Decidable p] (a b : Nat) :
    a + (if p then 1 else 0) + b = (if p then 1 else 0) + (b + a) := by
  omega

/-! ### R8. `Nat.zero_add`, `Nat.add_zero` · `0 + n = n`, `n + 0 = n` · goal (`simp` uses them itself) -/
example (n : Nat) (P : Nat → Prop) (h : P n) : P (0 + n) := by
  rw [Nat.zero_add]
  exact h

example (n : Nat) (P : Nat → Prop) (h : P n) : P (n + 0) := by
  rw [Nat.add_zero]
  exact h

/-! # Part W · Worked combination (not the exercise's loop) -/

/-! ### W1. A sum loop: generalise the start value, then specialise it to `0`
`sumLoop` adds up a list with a `for` loop. R1 turns it into a fold from `0`; the helper theorem
states what the fold does from ANY start value `c` (R4 → R2, R5 | R3, R6, R5, R7), and the main
theorem uses it at `c := 0` (R1, R6, R8). -/
def sumLoop (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

theorem foldl_sumL (xs : List Nat) (c : Nat) :
    xs.foldl (fun b a => b + a) c = c + sumL xs := by
  induction xs generalizing c with
    | nil => simp only [List.foldl_nil, sumL, Nat.add_zero]
    | cons x xs ih => simp only [List.foldl_cons, ih, sumL]; omega

example (xs : List Nat) : sumLoop xs = sumL xs := by
  simp only [sumLoop, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
  rw [foldl_sumL]
  rw [Nat.zero_add]

end M018Guide

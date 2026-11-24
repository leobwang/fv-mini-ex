/- Guide for H019 (Compiling expressions to a stack machine).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `H` in an entry is only there to finish the example; it shows what the goal became.
The entries work on toy objects (a counter machine `Cmd`/`run`, a binary tree `Tree`, a stack
function `pop2`), NOT on the exercise's `Expr`, `Instr`, `exec`, `compile`; every tactic behaves the
same way on both.
Part W: worked combinations on the toy objects.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace H019Guide

/-! ## The toy objects used by the entries -/

/-- A counter machine: two instructions acting on one number. -/
inductive Cmd where
  | inc
  | dbl

def act : Cmd → Nat → Nat
  | .inc, n => n + 1
  | .dbl, n => 2 * n

/-- Run a program: execute the head instruction, then the rest (shaped like the exercise's `exec`). -/
def run : List Cmd → Nat → Nat
  | [], n => n
  | c :: cs, n => run cs (act c n)

/-- A binary tree with numbers at the leaves: two recursive arguments, like `Expr.add a b`. -/
inductive Tree where
  | leaf (n : Nat)
  | node (l r : Tree)

def flat : Tree → List Nat
  | .leaf n => [n]
  | .node l r => flat l ++ flat r

/-- `flat` with an accumulator `k`: no `++` (shaped like the exercise's `compileAcc`). -/
def flatAcc : Tree → List Nat → List Nat
  | .leaf n, k => n :: k
  | .node l r, k => flatAcc l (flatAcc r k)

/-- Pop two numbers, push their sum; any other stack is left alone (shaped like `step`). -/
def pop2 : List Nat → List Nat
  | b :: a :: s => (a + b) :: s
  | s => s

/-! # Part R · Reference entries -/

/-! ## Induction with a generalized argument -/

/-! ### R1. `induction l generalizing s with | nil => … | cons x l ih => …` · goal list: one goal per
constructor of `List`; `ih` holds for EVERY `s`
`generalizing s` takes `s` out of the context before inducting, so each IH starts with `∀ s`. -/
example {α β : Type} (P : List α → β → Prop) (l : List α) (s : β)
    (H0 : ∀ s, P [] s) (H1 : ∀ x l s, (∀ s', P l s') → P (x :: l) s) : P l s := by
  induction l generalizing s with
    | nil => ?_
    | cons x l ih => ?_
  exact H0 s
  exact H1 x l s ih

/-! ### R2. `rfl` · closes an equation whose two sides compute to the same term
Both sides are unfolded by the defining equations of `run` and `++` on constructors (`[]`, `x :: l`). -/
example (cs : List Cmd) (n : Nat) : run ([] ++ cs) n = run cs (run [] n) := by
  rfl

/-! ### R3. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal
`a :: as ++ bs` means `(a :: as) ++ bs`: `::` binds tighter than `++`. -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (H : P (a :: (as ++ bs))) :
    P (a :: as ++ bs) := by
  rw [List.cons_append]
  exact H

/-! ### R4. `simp only [f]` · goal: `f` applied to a constructor → the right side of `f`'s equation -/
example (c : Cmd) (cs : List Cmd) (n : Nat) (P : Nat → Prop) (H : P (run cs (act c n))) :
    P (run (c :: cs) n) := by
  simp only [run]
  exact H

/-! ### R5. `simp only [ih]` with `ih : ∀ m, f m = g m` · goal: `f t` → `g t` for whatever `t` is there
`simp` (and `rw`) choose the instance `m := t` by matching. -/
example (f g : Nat → Nat) (ih : ∀ m, f m = g m) (k : Nat) (P : Nat → Prop) (H : P (g (k + 1))) :
    P (f (k + 1)) := by
  simp only [ih]
  exact H

/-! ### R6. `induction t generalizing k with | leaf n => … | node l r ihl ihr => …` · goal list: one
goal per constructor of your own type; one IH per recursive argument -/
example (P : Tree → List Nat → Prop) (t : Tree) (k : List Nat) (H0 : ∀ n k, P (.leaf n) k)
    (H1 : ∀ l r k, (∀ k', P l k') → (∀ k', P r k') → P (.node l r) k) : P t k := by
  induction t generalizing k with
    | leaf n => ?_
    | node l r ihl ihr => ?_
  exact H0 n k
  exact H1 l r k ihl ihr

/-! ## Lists: `++` and `[]` -/

/-! ### R7. `List.append_assoc` · `as ++ bs ++ cs = as ++ (bs ++ cs)` · goal
`++` groups to the left, so `as ++ bs ++ cs` is `(as ++ bs) ++ cs`. -/
example {α : Type} (as bs cs : List α) (P : List α → Prop) (H : P (as ++ (bs ++ cs))) :
    P (as ++ bs ++ cs) := by
  rw [List.append_assoc]
  exact H

/-! ### R8. `rw [L]` / `simp [L]` with an equation lemma `L` proved earlier · goal
`List.foldl_append : List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l) l'` stands in for
any lemma of your own: its arguments are found by matching the left side in the goal. -/
example {α β : Type} (f : β → α → β) (b : β) (l l' : List α) (P : β → Prop)
    (H : P (List.foldl f (List.foldl f b l) l')) : P (List.foldl f b (l ++ l')) := by
  rw [List.foldl_append]
  exact H

/-! ### R9. `simp only [f]` on a `match` with a catch-all `_` case · goal: fires only when the
argument visibly has the shape of an earlier case (`b :: a :: s`); on a bare variable it does nothing -/
example (a b : Nat) (s : List Nat) (P : List Nat → Prop) (H : P ((a + b) :: s)) :
    P (pop2 (b :: a :: s)) := by
  simp only [pop2]
  exact H

/-! ### R10. `List.nil_append` · `[] ++ as = as` · goal
With R3 it turns `[x] ++ k` (that is, `x :: [] ++ k`) into `x :: k`. -/
example {α : Type} (as : List α) (P : List α → Prop) (H : P as) : P ([] ++ as) := by
  rw [List.nil_append]
  exact H

/-! ## Using a general lemma at a particular argument -/

/-! ### R11. `exact H []` (or the term `H []`) · closes the goal with a `∀` lemma at a chosen argument
`[a]` is notation for `a :: []`, so `H []` has exactly the type `f [] = [a]`. -/
example (f : List Nat → List Nat) (a : Nat) (H : ∀ s, f s = a :: s) : f [] = [a] := by
  exact H []

/-! ### R12. `List.append_nil` · `as ++ [] = as` · goal -/
example {α : Type} (as : List α) (P : List α → Prop) (H : P as) : P (as ++ []) := by
  rw [List.append_nil]
  exact H

/-! ### R13. `rw [L]` closes the goal · after rewriting, `rw` tries `rfl` -/
example (f g : List Nat → List Nat) (L : ∀ s, f s = g s) : f [] = g [] := by
  rw [L]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `run` distributes over `++`: R1, then R2 / R3, R4, R5 -/
example (cs ds : List Cmd) (n : Nat) : run (cs ++ ds) n = run ds (run cs n) := by
  induction cs generalizing n with
    | nil => rfl
    | cons c cs ih => simp only [List.cons_append, run, ih]

/-! ### W2. The accumulator version equals the `++` version: R6, then R2 / R4, R5, R7 -/
example (t : Tree) (k : List Nat) : flatAcc t k = flat t ++ k := by
  induction t generalizing k with
    | leaf n => rfl
    | node l r ihl ihr => simp only [flatAcc, flat, ihl, ihr, List.append_assoc]

/-! ### W3. Why `generalizing` matters: the IH is used at a stack other than the original `k`
In W2's `node` case `ihr` is used at `k` but `ihl` at `flat r ++ k`. Without `generalizing k`,
`ihl : flatAcc l k = flat l ++ k` would hold for the original `k` only, and the step would fail. -/
example (l r : Tree) (k : List Nat) (ihl : ∀ k', flatAcc l k' = flat l ++ k')
    (ihr : ∀ k', flatAcc r k' = flat r ++ k') : flatAcc (.node l r) k = flat (.node l r) ++ k := by
  simp only [flatAcc]
  rw [ihr]
  rw [ihl]
  simp only [flat]
  rw [List.append_assoc]

/-! ### W4. Running the stack function on a concrete stack: R9 needs the shape `b :: a :: s` -/
example (s : List Nat) : pop2 (pop2 (3 :: 2 :: 1 :: s)) = 6 :: s := by
  simp only [pop2]

end H019Guide

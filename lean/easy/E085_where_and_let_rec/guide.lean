/- Guide for E085 (where and let rec).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use two small accumulator functions of their own, `ones` (helper via `where`) and `len`
(helper via `let rec`); they are not the exercise's `countdown` / `sumList`.
Part W: worked combinations on `rev` (list reversal with an accumulator) and on `len`.
Assumed: Lean basics (E001–E033).
-/

namespace E085Guide

/-- `ones n` is the list of `n` ones. The helper `ones.aux` is declared with `where`: it becomes a
separate top-level function named `ones.aux`, with its own equations. -/
def ones (n : Nat) : List Nat := aux n []
where
  aux : Nat → List Nat → List Nat
    | 0, acc => acc
    | k + 1, acc => aux k (1 :: acc)

/-- `len l` is the length of `l`. The helper is declared with `let rec` inside the body; it also
becomes a top-level function, `len.run`, with its own equations. -/
def len (l : List Nat) : Nat :=
  let rec run : List Nat → Nat → Nat
    | [], n => n
    | _ :: t, n => run t (n + 1)
  run l 0

/-! # Part R · Reference entries -/

/-! ## Induction with an accumulator (Nat) -/

/-! ### R1. `induction n generalizing acc with | zero => … | succ k ih => …` · goal list and context
`generalizing acc` takes `acc` out of the context before the induction and puts it back in each case,
so `ih` is `∀ acc, …`: it holds for every accumulator, not only the one you started with. Arms `?_`
leave both cases as goals, so the infoview shows them. -/
example (P : Nat → List Nat → Prop) (h0 : ∀ acc, P 0 acc)
    (hs : ∀ k, (∀ acc, P k acc) → ∀ acc, P (k + 1) acc) (n : Nat) (acc : List Nat) : P n acc := by
  induction n generalizing acc with | zero => ?_ | succ k ih => ?_
  · exact h0 acc
  · exact hs k ih acc

/-- The same induction without `generalizing`: `ih : P k acc` is about the fixed `acc` only. -/
example (P : Nat → List Nat → Prop) (h : ∀ m a, P m a) (n : Nat) (acc : List Nat) : P n acc := by
  induction n with | zero => ?_ | succ k ih => ?_
  · exact h 0 acc
  · exact h (k + 1) acc

/-! ### R2. `rfl` · closes the base case: the helper's `0` equation computes, and so does `[] ++ acc` -/
example (acc : List Nat) : ones.aux 0 acc = [] ++ acc := by
  rfl

/-! ### R3. `simp only [f.aux]` · goal: one step of a `where` helper, by its own equation
`ones.aux (k + 1) acc` matches the pattern `k + 1, acc`, so it becomes `ones.aux k (1 :: acc)`: the
recursive call has a different accumulator. -/
example (k : Nat) (acc : List Nat) (P : List Nat → Prop) (h : P (ones.aux k (1 :: acc))) :
    P (ones.aux (k + 1) acc) := by
  simp only [ones.aux]
  exact h

/-! ### R4. `rw [ih]` with `ih : ∀ a, f a = g a` · goal: `f x` → `g x`, `a` chosen by matching
`rw` finds an instance `f x` in the goal and instantiates `a := x`. Here `x` is the new accumulator.
A proved theorem with arguments, `rw [thm]`, works the same way. -/
example {α β : Type} (f g : α → β) (ih : ∀ a, f a = g a) (x : α) (P : β → Prop) (h : P (g x)) :
    P (f x) := by
  rw [ih]
  exact h

/-! ### R5. `List.range_succ` · `List.range (n + 1) = List.range n ++ [n]` · goal
`List.range n` is the list `[0, 1, …, n - 1]`. -/
example (n : Nat) (P : List Nat → Prop) (h : P (List.range n ++ [n])) : P (List.range (n + 1)) := by
  rw [List.range_succ]
  exact h

/-! ### R6. `List.append_assoc` · `as ++ bs ++ cs = as ++ (bs ++ cs)` · goal
`++` groups to the left, so `as ++ bs ++ cs` is `(as ++ bs) ++ cs`. -/
example {α : Type} (as bs cs : List α) (P : List α → Prop) (h : P (as ++ (bs ++ cs))) :
    P (as ++ bs ++ cs) := by
  rw [List.append_assoc]
  exact h

/-! ### R7. `List.singleton_append` · `[x] ++ l = x :: l` · goal -/
example {α : Type} (x : α) (l : List α) (P : List α → Prop) (h : P (x :: l)) : P ([x] ++ l) := by
  rw [List.singleton_append]
  exact h

/-! ## The main function and its helper call -/

/-! ### R8. `simp only [f]` on a function with a `where` helper · goal: `f n` → the helper call -/
example (n : Nat) (P : List Nat → Prop) (h : P (ones.aux n [])) : P (ones n) := by
  simp only [ones]
  exact h

/-! ### R9. `List.append_nil` · `as ++ [] = as` · goal -/
example {α : Type} (as : List α) (P : List α → Prop) (h : P as) : P (as ++ []) := by
  rw [List.append_nil]
  exact h

/-! ## Induction with an accumulator (List) -/

/-! ### R10. `induction xs generalizing acc with | nil => … | cons x xs ih => …` · goal list and context
The `cons` case gets the head `x`, the tail `xs` and `ih : ∀ acc, …` about the tail. -/
example {α : Type} (P : List α → Nat → Prop) (hn : ∀ a, P [] a)
    (hc : ∀ x xs, (∀ a, P xs a) → ∀ a, P (x :: xs) a) (xs : List α) (acc : Nat) : P xs acc := by
  induction xs generalizing acc with | nil => ?_ | cons x xs ih => ?_
  · exact hn acc
  · exact hc x xs ih acc

/-! ### R11. `simp only [f.run]` · goal: one step of a `let rec` helper, by its own equation -/
example (x : Nat) (t : List Nat) (n : Nat) (P : Nat → Prop) (h : P (len.run t (n + 1))) :
    P (len.run (x :: t) n) := by
  simp only [len.run]
  exact h

/-! ### R12. `List.sum_nil` · `[].sum = 0` · goal
`xs.sum` (`List.sum xs`) adds up the elements: `[].sum = 0`, `(a :: l).sum = a + l.sum`. -/
example (P : Nat → Prop) (h : P 0) : P ([] : List Nat).sum := by
  rw [List.sum_nil]
  exact h

/-! ### R13. `List.sum_cons` · `(a :: l).sum = a + l.sum` · goal -/
example (a : Nat) (l : List Nat) (P : Nat → Prop) (h : P (a + l.sum)) : P (a :: l).sum := by
  rw [List.sum_cons]
  exact h

/-! ### R14. `omega` · closes linear arithmetic over `Nat`; `l.sum` counts as one unknown number -/
example (a b : Nat) (l : List Nat) : a + b + l.sum = a + (b + l.sum) := by
  omega

/-! ## The main function with a `let rec` helper -/

/-! ### R15. `simp only [f]` on a function with a `let rec` helper · goal: `f xs` → the helper call -/
example (xs : List Nat) (P : Nat → Prop) (h : P (len.run xs 0)) : P (len xs) := by
  simp only [len]
  exact h

/-! ### R16. `Nat.zero_add` · `0 + n = n` · goal -/
example (n : Nat) (P : Nat → Prop) (h : P n) : P (0 + n) := by
  rw [Nat.zero_add]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- List reversal with an accumulator: `rev.aux xs acc` pushes the elements of `xs` onto `acc`. -/
def rev {α : Type} (xs : List α) : List α := aux xs []
where
  aux : List α → List α → List α
    | [], acc => acc
    | x :: t, acc => aux t (x :: acc)

/-! ### W1. The helper invariant for every accumulator: R10, R3 (for `rev.aux`), R4, then
`List.reverse_cons : (a :: as).reverse = as.reverse ++ [a]`, R6, R7. -/
theorem rev_aux_eq {α : Type} (xs acc : List α) : rev.aux xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with | nil => rfl | cons x t ih => ?_
  simp only [rev.aux]
  rw [ih]
  rw [List.reverse_cons]
  rw [List.append_assoc, List.singleton_append]

/-! ### W2. The main fact from the invariant at `acc := []`: R8, R4 (with the theorem), R9 -/
example {α : Type} (xs : List α) : rev xs = xs.reverse := by
  simp only [rev]
  rw [rev_aux_eq, List.append_nil]

/-! ### W3. `len`: R10, R11 with `List.length_cons : (a :: l).length = l.length + 1`, R4, R14;
then the main fact by R15, R4 (with the theorem), R16. -/
theorem len_run_eq (xs : List Nat) (n : Nat) : len.run xs n = n + xs.length := by
  induction xs generalizing n with | nil => rfl | cons x t ih => ?_
  simp only [len.run, List.length_cons]
  rw [ih]
  omega

example (xs : List Nat) : len xs = xs.length := by
  simp only [len]
  rw [len_run_eq, Nat.zero_add]

end E085Guide

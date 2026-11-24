/- Guide for E015 (Induction on lists).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use `induction xs with | nil => ?_ | cons x xs ih => ?_` so that both cases show up as
goals in the infoview; in the exercise you may put the tactics right after each `=>` instead.
Part W: worked combinations on `total` (sum of a list) and `dbl` (double every element), not on the
exercise's `len` / `app`.
Assumed: Lean basics up to E014 (`rfl`, `exact`, `simp`, `omega`, `induction` on `Nat`).
-/

namespace E015Guide

/-- `total xs` is the sum of the elements of `xs`. -/
def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs

/-- `dbl xs` doubles every element of `xs`. -/
def dbl : List Nat → List Nat
  | [] => []
  | x :: xs => 2 * x :: dbl xs

/-! # Part R · Reference entries -/

/-! ## Splitting a list -/

/-! ### R1. `induction xs with | nil => ?_ | cons x xs ih => ?_` · goal list: one goal → two goals
Case `nil`: `xs` is replaced by `[]`. Case `cons`: `xs` is replaced by `x :: xs`, and the context
gains the head `x`, the tail `xs` and the induction hypothesis `ih`, the goal for the tail. -/
example {α : Type} (P : List α → Prop) (h0 : P []) (hs : ∀ x xs, P xs → P (x :: xs))
    (xs : List α) : P xs := by
  induction xs with | nil => ?_ | cons x xs ih => ?_
  · exact h0
  · exact hs x xs ih

/-! ## The `nil` case -/

/-! ### R2. `rfl` · closes a goal whose two sides compute to the same term
`dbl []` computes to `[]` by the first equation of `dbl`, so both sides are `[]`. -/
example : dbl [] = [] := by
  rfl

/-! ## The `cons` case -/

/-! ### R3. `simp [f]` · goal: `f (x :: xs)` → the right side of `f`'s `x :: xs` equation
`simp [total]` uses the equations `total [] = 0` and `total (x :: xs) = x + total xs`; it rewrites
wherever the argument literally is `[]` or `_ :: _`, and repeats until nothing applies. -/
example (x : Nat) (xs : List Nat) (P : Nat → Prop) (h : P (x + total xs)) :
    P (total (x :: xs)) := by
  simp [total]
  exact h

/-! ### R4. `simp` (lemma `List.cons.injEq`) · goal: `x :: a = x :: b` → `a = b`
Two lists with the same head are equal exactly when their tails are: `simp` peels the head off. -/
example {α : Type} (x : α) (a b : List α) (h : a = b) : x :: a = x :: b := by
  simp
  exact h

/-! ### R5. `simp [f, ih]` · goal: unfold `f`, then rewrite the left side of `ih` to its right side
Here `ih : total (dbl xs) = 2 * total xs`. After unfolding `dbl` and `total` once, the goal contains
`total (dbl xs)`, which `ih` turns into `2 * total xs`. -/
example (x : Nat) (xs : List Nat) (ih : total (dbl xs) = 2 * total xs) (P : Nat → Prop)
    (h : P (2 * x + 2 * total xs)) : P (total (dbl (x :: xs))) := by
  simp [dbl, total, ih]
  exact h

/-! ## Arithmetic left over -/

/-! ### R6. `simp [f]` · closes a `nil` goal that `rfl` cannot: `0 + n = n`
`total [] + total ys` computes to `0 + total ys`, but `0 + n` does not compute to `n` for an unknown
`n` (`Nat.add` recurses on its second argument), so `rfl` fails. `simp` knows `0 + n = n`. -/
example (ys : List Nat) : total [] + total ys = total ys := by
  simp [total]

/-! ### R7. `omega` · closes linear arithmetic over `Nat`; `f xs` counts as one unknown number -/
example (f : List Nat → Nat) (xs ys : List Nat) : 2 + f xs + f ys = f ys + (f xs + 2) := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Lists out, `++` in: R1, R2 for `nil`, one `simp [dbl, ih]` for `cons` (R3, R4, R5)
`x :: xs ++ ys` means `x :: (xs ++ ys)`; `simp` also uses `List.cons_append` to move `x` out. -/
example (xs ys : List Nat) : dbl (xs ++ ys) = dbl xs ++ dbl ys := by
  induction xs with | nil => ?_ | cons x xs ih => ?_
  · rfl
  simp [dbl]
  exact ih

/-! ### W2. Numbers out: R1, R6 for `nil`, R5 then R7 for `cons`
`simp` stops at an equation of sums it cannot reorder; `omega` finishes it. -/
example (xs : List Nat) : total (dbl xs) = 2 * total xs := by
  induction xs with | nil => ?_ | cons x xs ih => ?_
  · simp [dbl, total]
  simp [dbl, total, ih]
  omega

end E015Guide

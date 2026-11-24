/- Guide for M001 (take and drop).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on the toy function `insertAt` below, which is NOT the exercise's.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M001Guide

/-! ## Toy object used by the entries (not the exercise's) -/

/-- `insertAt a n xs`: put `a` at position `n` of `xs` (at the end if `xs` is shorter).
Like the exercise's functions it recurses on the number and the list at the same time. -/
def insertAt {α : Type} (a : α) : Nat → List α → List α
  | 0, xs => a :: xs
  | _ + 1, [] => [a]
  | n + 1, x :: xs => x :: insertAt a n xs

/-! # Part R · Reference entries -/

/-! ## Induction with a re-quantified hypothesis; case split on the list -/

/-! ### R1. `induction n generalizing xs` · goal list: `zero` and `succ`; context: `ih` is `∀ xs, …`
`generalizing xs` takes `xs` out of the context first, so the induction hypothesis holds for EVERY
list, in particular the tail `xs'` you meet later. Without it, `ih` speaks only about the original
`xs`. Write `induction n generalizing xs with | zero => … | succ n ih => …` to name `n✝` and `ih`.
`‹_›` below means "the hypothesis in context whose type fits here" (here the unnamed IH `a✝`). -/
example {α : Type} (P : Nat → List α → Prop) (h0 : ∀ xs, P 0 xs)
    (hs : ∀ n, (∀ xs, P n xs) → ∀ xs, P (n + 1) xs) (n : Nat) (xs : List α) : P n xs := by
  induction n generalizing xs
  exact h0 xs
  exact hs _ ‹_› xs

/-- R1 without `generalizing`: the hypothesis is only about the fixed `xs`. -/
example {α : Type} (xs : List α) (P : Nat → List α → Prop) (h0 : P 0 xs)
    (hs : ∀ n, P n xs → P (n + 1) xs) (n : Nat) : P n xs := by
  induction n
  exact h0
  exact hs _ ‹_›

/-! ### R2. `cases xs` · goal list: one goal per constructor, `[]` and `head :: tail`
Write `cases xs with | nil => … | cons x xs => …` to name the head and tail. -/
example {α : Type} (P : List α → Prop) (h0 : P []) (hc : ∀ x xs, P (x :: xs)) (xs : List α) :
    P xs := by
  cases xs
  exact h0
  exact hc _ _

/-! ## Unfolding a definition by pattern matching -/

/-! ### R3. `simp only [f]` · goal: one equation of `f` applied where the arguments are literally
a constructor pattern (`0`, `n + 1`, `[]`, `x :: xs`). `simp [f]` does the same and keeps going.
Each `| pattern => body` line of a `def` is one equation `f pattern = body`. -/
example {α : Type} (a x : α) (n : Nat) (xs : List α) (P : List α → Prop)
    (h : P (x :: insertAt a n xs)) : P (insertAt a (n + 1) (x :: xs)) := by
  simp only [insertAt]
  exact h

example {α : Type} (a : α) (xs : List α) (P : List α → Prop) (h : P (a :: xs)) :
    P (insertAt a 0 xs) := by
  simp only [insertAt]
  exact h

/-! ## List algebra (`simp` applies these by itself) -/

/-! ### R4. `List.nil_append` · `[] ++ l = l` · goal -/
example {α : Type} (l : List α) (P : List α → Prop) (h : P l) : P ([] ++ l) := by
  rw [List.nil_append]
  exact h

/-! ### R5. `List.append_nil` · `l ++ [] = l` · goal -/
example {α : Type} (l : List α) (P : List α → Prop) (h : P l) : P (l ++ []) := by
  rw [List.append_nil]
  exact h

/-! ### R6. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal
`::` binds tighter than `++`: `a :: as ++ bs` means `(a :: as) ++ bs`. -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (h : P (a :: (as ++ bs))) :
    P (a :: as ++ bs) := by
  rw [List.cons_append]
  exact h

/-! ### R7. `simp [ih]` with `ih : ∀ xs, l xs = r xs` · goal: `simp` instantiates the `∀` at
whatever list it finds (here the tail `t`), rewrites left to right, and closes `a = a`.
A helper lemma `simp [my_lemma]` is used the same way. -/
example {α : Type} (f g : List α → List α) (x : α) (t : List α) (ih : ∀ xs, f xs = g xs) :
    x :: f t = x :: g t := by
  simp [ih]

/-! ### R8. `List.length_nil`, `List.length_cons` · `[].length = 0`, `(a :: l).length = l.length + 1` -/
example {α : Type} (P : Nat → Prop) (h : P 0) : P ([] : List α).length := by
  rw [List.length_nil]
  exact h

example {α : Type} (a : α) (l : List α) (P : Nat → Prop) (h : P (l.length + 1)) :
    P (a :: l).length := by
  rw [List.length_cons]
  exact h

/-! ## Natural-number subtraction and `min` (`simp` applies these by itself) -/

/-! ### R9. `Nat.sub_zero` · `n - 0 = n` · goal -/
example (n : Nat) (P : Nat → Prop) (h : P n) : P (n - 0) := by
  rw [Nat.sub_zero]
  exact h

/-! ### R10. `Nat.zero_sub` · `0 - n = 0` · goal
`-` on `Nat` is truncated: a result below zero is `0`. `simp` proves this one via
`Nat.sub_eq_zero_of_le : n ≤ m → n - m = 0`. -/
example (n : Nat) (P : Nat → Prop) (h : P 0) : P (0 - n) := by
  rw [Nat.zero_sub]
  exact h

/-! ### R11. `Nat.add_sub_add_right` · `n + k - (m + k) = n - m` · goal
`simp` does this step with the built-in simplification procedure `Nat.reduceSubDiff`. -/
example (n m : Nat) (P : Nat → Prop) (h : P (n - m)) : P (n + 1 - (m + 1)) := by
  rw [Nat.add_sub_add_right]
  exact h

/-! ### R12. `Nat.zero_min`, `Nat.min_zero` · `min 0 a = 0`, `min a 0 = 0` · goal -/
example (a : Nat) (P : Nat → Prop) (h : P 0) : P (min 0 a) := by
  rw [Nat.zero_min]
  exact h

example (a : Nat) (P : Nat → Prop) (h : P 0) : P (min a 0) := by
  rw [Nat.min_zero]
  exact h

/-! ### R13. `Nat.add_min_add_right` · `min (a + c) (b + c) = min a b + c` · goal -/
example (a b : Nat) (P : Nat → Prop) (h : P (min a b + 1)) : P (min (a + 1) (b + 1)) := by
  rw [Nat.add_min_add_right]
  exact h

/-! ### R14. `Nat.zero_add` · `0 + n = n` · goal
`n + 0 = n` holds by computation (`+` recurses on its second argument); `0 + n = n` needs this lemma. -/
example (n : Nat) (P : Nat → Prop) (h : P n) : P (0 + n) := by
  rw [Nat.zero_add]
  exact h

/-! ## A helper lemma; reshaping a number so a pattern matches -/

/-! ### R15. `cases m <;> rfl` · goal list: one goal per case of `m`, each closed by computation
Use it for a fact like `insertAt a m [] = [a]`: for `m = 0` and `m = n + 1` the definition
reduces, but for an unknown `m` it does not, so split first. State such a fact as its own
`theorem` (outside the spec regions) and pass it to `simp` (R7). -/
example {α : Type} (a : α) (m : Nat) : insertAt a m [] = [a] := by
  cases m <;> rfl

/-! ### R16. `rw [show a = b by omega]` · goal: `a` replaced by `b`, a side fact proved on the spot
`simp [f]` only unfolds `f (n + 1) …` when the number is literally `_ + 1`. `n + 1 + m` is
`(n + 1) + m`, which is not; rewrite it to `(n + m) + 1` first (W2). -/
example (n m : Nat) (P : Nat → Prop) (h : P (n + m + 1)) : P (n + 1 + m) := by
  rw [show n + 1 + m = n + m + 1 by omega]
  exact h

/-! ### R17. `omega` · closes linear arithmetic over `Nat` and `Int`
It knows truncated `-`, `min`, `max`, `+`, `*` by numerals, `≤`, `<`, `=`, and it uses the
hypotheses in the context. A backup when `simp` leaves an arithmetic goal open. -/
example (a b c : Nat) (h : a ≤ b) : min (a + c) (b + c) - c = a := by
  omega

/-! # Part W · Worked combinations (on `insertAt`, not the exercise's functions) -/

/-- W1. Induction on the number generalizing the list (R1), then a case split on the list (R2),
then `simp` with the definition and the IH (R3, R8, R7). -/
theorem length_insertAt {α : Type} (a : α) (n : Nat) (xs : List α) :
    (insertAt a n xs).length = xs.length + 1 := by
  induction n generalizing xs with
    | zero => simp [insertAt]
    | succ n ih =>
      cases xs with
        | nil => simp [insertAt]
        | cons x xs => simp [insertAt, ih]

/-- W2. Reshape the number before unfolding (R16), and a helper lemma for the empty list (R15). -/
theorem insertAt_nil {α : Type} (a : α) (m : Nat) : insertAt a m [] = [a] := by
  cases m <;> rfl

example {α : Type} (a x : α) (n m : Nat) (xs : List α) :
    insertAt a (n + 1 + m) (x :: xs) = x :: insertAt a (n + m) xs := by
  rw [show n + 1 + m = n + m + 1 by omega]
  simp [insertAt]

example {α : Type} (a : α) (n m : Nat) : insertAt a (n + 1 + m) [] = [a] := by
  simp [insertAt_nil]

end M001Guide

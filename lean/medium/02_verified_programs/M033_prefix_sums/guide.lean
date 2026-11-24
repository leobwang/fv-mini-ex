/- Guide for M033 (Prefix sums).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about a list-building recursion use the guide's own function `marks` below, which is
NOT the exercise's `prefixSums`. Case alternatives are written `| nil => ?_` so every case stays open
as a goal you can inspect; in the exercise you write a tactic after `=>` instead.
Part W: worked combinations on `marks`.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M033Guide

/-- `marks l = [0, 1, …, l.length]`: one more entry than `l`. The tail is built from the recursive
result by adding 1 to every entry. -/
def marks (l : List Nat) : List Nat :=
  match l with
  | [] => [0]
  | _ :: t => 0 :: (marks t).map (· + 1)

/-! # Part R · Reference entries -/

/-! ## Building a list by recursion -/

/-! ### R1. `match l with | [] => … | x :: t => … (f t) …` · closes a test goal
A function from lists to lists, by structural recursion: one arm per constructor, the recursive call
on the tail `t`. Lean accepts it without `termination_by`, and it computes inside proofs, so `rfl`
or `decide` can test it. A pattern variable that the arm does not use is written `_`. -/
example : marks [7, 7, 7] = [0, 1, 2, 3] := by
  rfl

/-! ### R2. `List.map f l` and the section `(c + ·)` · closes a test goal
`List.map f l` (also written `l.map f`) applies `f` to every entry. `(c + ·)` is notation for
`fun x => c + x`; the infoview prints the function in that `fun` form. -/
example : [1, 2, 3].map (10 + ·) = [11, 12, 13] := by
  rfl

/-! ## Length: induction on the list -/

/-! ### R3. `induction l with | nil => … | cons x t ih => …` · goal list
One goal per constructor. In `cons`, `ih` is the statement for the tail `t`. -/
example {α : Type} (l : List α) (P : List α → Prop) (h0 : P []) (hs : ∀ x t, P t → P (x :: t)) :
    P l := by
  induction l with
    | nil => ?_
    | cons x t ih => ?_
  · exact h0
  · exact hs x t ih

/-! ### R4. `simp only [f]` · goal: `f (x :: t)` → the right-hand side of the `cons` arm
Naming a function defined by `match` hands its equations to `simp` (one per arm), so `f` applied to
a constructor is unfolded. `simp [f, …]` does the same and keeps simplifying. -/
example (x : Nat) (t : List Nat) (P : List Nat → Prop) (h : P (0 :: (marks t).map (· + 1))) :
    P (marks (x :: t)) := by
  simp only [marks]
  exact h

/-! ### R5. `List.length_cons` · `(a :: as).length = as.length + 1` · goal -/
example {α : Type} (a : α) (l : List α) (P : Nat → Prop) (h : P (l.length + 1)) :
    P (a :: l).length := by
  rw [List.length_cons]
  exact h

/-! ### R6. `List.length_map` · `(List.map f as).length = as.length` · goal -/
example {α β : Type} (f : α → β) (l : List α) (P : Nat → Prop) (h : P l.length) :
    P (l.map f).length := by
  rw [List.length_map]
  exact h

/-! ## Indexing: induction with a varying index -/

/-! ### R7. `induction l generalizing i with …` · context: `i` and `h` are bound again in each case
Without `generalizing`, the IH is about the one fixed `i` you started with, and the step needs it at
a different index. With it, `i` (and every hypothesis mentioning `i`, here `h`) is taken into the
induction: each case gets a fresh `i` and `h`, and `ih` holds for every index `∀ (i : Nat), …`. -/
example {α : Type} (l : List α) (i : Nat) (h : i ≤ l.length) (P : List α → Nat → Prop)
    (h0 : ∀ i, i ≤ ([] : List α).length → P [] i)
    (hs : ∀ x t, (∀ i, i ≤ t.length → P t i) → ∀ i, i ≤ (x :: t).length → P (x :: t) i) :
    P l i := by
  induction l generalizing i with
    | nil => ?_
    | cons x t ih => ?_
  · exact h0 i h
  · exact hs x t ih i h

/-! ### R8. `simp at h` on a bound by the empty list · context: `h : i ≤ [].length` → `h : i = 0`
`simp` uses `List.length_nil` (`[].length = 0`) and `Nat.le_zero_eq` (`(i ≤ 0) = (i = 0)`). -/
example {α : Type} (i : Nat) (h : i ≤ ([] : List α).length) (P : Nat → Prop) (hp : i = 0 → P i) :
    P i := by
  simp at h
  exact hp h

/-! ### R9. `subst h` · context loses `i` and `h : i = 0`; goal: every `i` → `0` -/
example (i : Nat) (h : i = 0) (P : Nat → Prop) (hp : P 0) : P i := by
  subst h
  exact hp

/-! ### R10. `cases i with | zero => … | succ i => …` · goal list: index `0` and index `i + 1`
A hypothesis that mentions `i` is rewritten in each goal. -/
example (n i : Nat) (h : i ≤ n) (P : Nat → Prop) (h0 : P 0) (hs : ∀ j, j + 1 ≤ n → P (j + 1)) :
    P i := by
  cases i with
    | zero => ?_
    | succ i => ?_
  · exact h0
  · exact hs i h

/-! ### R11. `rfl` at index `0` · closes `(a :: l)[0]? = some (List.take 0 t).sum`
Both sides compute: `(a :: l)[0]?` is `some a` (`List.getElem?_cons_zero`), `List.take 0 t` is `[]`
(`List.take_zero`) and `[].sum` is `0` (`List.sum_nil`). `l[i]?` is the entry at index `i` as an
`Option`: `some _` if `i < l.length`, `none` otherwise. -/
example (l t : List Int) : ((0 : Int) :: l)[0]? = some (List.take 0 t).sum := by
  rfl

/-! ### R12. `simp at h` on a bound by a `cons` · context: `h : i + 1 ≤ (x :: l).length` → `h : i ≤ l.length`
`simp` uses R5 and then cancels `+ 1` (`Nat.add_le_add_iff_right`). -/
example {α : Type} (x : α) (l : List α) (i : Nat) (h : i + 1 ≤ (x :: l).length) (P : Prop)
    (hp : i ≤ l.length → P) : P := by
  simp at h
  exact hp h

/-! ### R13. `List.getElem?_cons_succ` · `(a :: l)[i + 1]? = l[i]?` · goal: drop the head, shift the index -/
example {α : Type} (a : α) (l : List α) (i : Nat) (P : Option α → Prop) (h : P l[i]?) :
    P (a :: l)[i + 1]? := by
  rw [List.getElem?_cons_succ]
  exact h

/-! ### R14. `List.getElem?_map` · `(List.map f l)[i]? = Option.map f l[i]?` · goal
Indexing commutes with `map`. `Option.map f` applies `f` inside `some`, and keeps `none`. -/
example {α β : Type} (f : α → β) (l : List α) (i : Nat) (P : Option β → Prop)
    (h : P (Option.map f l[i]?)) : P (l.map f)[i]? := by
  rw [List.getElem?_map]
  exact h

/-! ### R15. `ih i (by omega)` · context gains the IH at index `i`
An IH `ih : ∀ (i : Nat), i ≤ n → Q i` is a function: give it the index and a proof of the bound.
`(by omega)` proves the bound from the hypotheses in the context. The term can go straight into
`simp [ih i (by omega)]` or `rw [ih i (by omega)]` as a rewrite rule. -/
example (n i : Nat) (Q : Nat → Prop) (ih : ∀ (i : Nat), i ≤ n → Q i) (h : i ≤ n) (P : Prop)
    (hp : Q i → P) : P := by
  have hi := ih i (by omega)
  exact hp hi

/-! ### R16. `Option.map_some` · `Option.map f (some a) = some (f a)` · goal -/
example {α β : Type} (f : α → β) (a : α) (P : Option β → Prop) (h : P (some (f a))) :
    P (Option.map f (some a)) := by
  rw [Option.map_some]
  exact h

/-! ### R17. `List.take_succ_cons` · `List.take (i + 1) (a :: as) = a :: List.take i as` · goal -/
example {α : Type} (a : α) (l : List α) (i : Nat) (P : List α → Prop) (h : P (a :: l.take i)) :
    P ((a :: l).take (i + 1)) := by
  rw [List.take_succ_cons]
  exact h

/-! ### R18. `List.sum_cons` · `(a :: l).sum = a + l.sum` · goal
`[Add α] [Zero α]`: `α` has `+` and `0` (`Nat` and `Int` do); `[].sum = 0`. -/
example {α : Type} [Add α] [Zero α] (a : α) (l : List α) (P : α → Prop) (h : P (a + l.sum)) :
    P (a :: l).sum := by
  rw [List.sum_cons]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `marks` has one more entry than its argument: R3, then `rfl` and `simp [marks, ih]` (R4–R6) -/
example (l : List Nat) : (marks l).length = l.length + 1 := by
  induction l with
    | nil => rfl
    | cons x t ih => simp [marks, ih]

/-! ### W2. One index step of `marks`, rewrite by rewrite: R4, R13, R14, the IH, R16 -/
example (x : Nat) (t : List Nat) (i : Nat) (ih : (marks t)[i]? = some i) :
    (marks (x :: t))[i + 1]? = some (i + 1) := by
  simp only [marks]
  rw [List.getElem?_cons_succ]
  rw [List.getElem?_map]
  rw [ih]
  rw [Option.map_some]

/-! ### W3. A sum over a `take` of a `cons`, unfolded: R17, R18 twice; `simp` clears `take 0`, `[].sum`, `+ 0` -/
example (a b : Int) (l : List Int) : ((a :: b :: l).take 2).sum = a + b := by
  rw [List.take_succ_cons]
  rw [List.sum_cons]
  rw [List.take_succ_cons]
  rw [List.sum_cons]
  simp

end M033Guide

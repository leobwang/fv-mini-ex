/- Guide for M016 (Reverse with an accumulator).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own objects, which are NOT the exercise's:
  `dupAcc xs acc`  tail-recursive with an accumulator: pushes every element of `xs` TWICE onto `acc`;
  `lenAcc xs n`    tail-recursive length: adds 1 to the counter `n` per element.
Part W: worked combinations on these objects.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M016Guide

/-- `dupAcc xs acc`: walk `xs`, pushing each element twice onto the front of `acc`. -/
def dupAcc {β : Type} : List β → List β → List β
  | [], acc => acc
  | y :: ys, acc => dupAcc ys (y :: y :: acc)

/-- `lenAcc xs n`: `n` plus the length of `xs`, counted with an accumulator. -/
def lenAcc {β : Type} : List β → Nat → Nat
  | [], n => n
  | _ :: ys, n => lenAcc ys (n + 1)

/-! # Part R · Reference entries -/

/-! ## Induction with a varying accumulator -/

/-! ### R1. `induction xs generalizing acc with | nil => … | cons x xs ih => …` · goal list
Plain `induction xs` fixes `acc` once for the whole proof, so `ih` speaks only about that `acc`.
`generalizing acc` first puts `acc` back into the goal (`∀ acc, …`), inducts, and re-introduces it in
each case, so `ih : ∀ acc, …` holds for EVERY accumulator, in particular for `x :: acc`.
The arms here are `?_`, so both goals stay open; in a proof you write tactics after `=>`. -/
example {α : Type} (P : List α → List α → Prop) (h0 : ∀ acc, P [] acc)
    (h1 : ∀ x xs, (∀ acc, P xs acc) → ∀ acc, P (x :: xs) acc) (xs acc : List α) : P xs acc := by
  induction xs generalizing acc with | nil => ?_ | cons x xs ih => ?_
  · exact h0 acc
  · exact h1 x xs ih acc

/-! ### R2. `rfl` · closes an equation whose two sides compute to the same value
`dupAcc [] acc` computes to `acc` (first clause); `[].reverse ++ acc` computes to `acc` too
(`[].reverse` is `[]`, and `[] ++ l` is `l` by the definition of `++`). -/
example {β : Type} (acc : List β) : dupAcc [] acc = ([] : List β).reverse ++ acc := by
  rfl

/-! ### R3. `simp only [f]` · goal: unfold the `::` clause of a pattern-matching `def`
A call is unfolded only when its list argument is visibly `[]` or `_ :: _`. The same works for a
non-recursive `def` such as `def g xs := f xs []`: `simp only [g]` replaces `g xs` by `f xs []`. -/
example {β : Type} (P : List β → Prop) (y : β) (ys acc : List β) (h : P (dupAcc ys (y :: y :: acc))) :
    P (dupAcc (y :: ys) acc) := by
  simp only [dupAcc]
  exact h

/-! ### R4. `rw [ih]` with `ih : ∀ acc, f xs acc = g xs ++ acc` · goal: `f xs t` → `g xs ++ t`
`rw` instantiates the `∀` itself: it finds `f xs (x :: acc)` in the goal and uses `ih (x :: acc)`.
This is why R1 needs `generalizing`: with `ih : f xs acc = …` for the ORIGINAL `acc` only, the
pattern `f xs acc` does not occur in a goal about `f xs (x :: acc)`, and `rw` fails. -/
example {α : Type} (f : List α → List α → List α) (g : List α → List α) (x : α) (xs acc : List α)
    (ih : ∀ acc, f xs acc = g xs ++ acc) (P : List α → Prop) (h : P (g xs ++ x :: acc)) :
    P (f xs (x :: acc)) := by
  rw [ih]
  exact h

/-! ## List lemmas: `reverse` and `++` -/

/-! ### R5. `List.reverse_cons` · `(a :: as).reverse = as.reverse ++ [a]` · goal -/
example {α : Type} (a : α) (l : List α) (P : List α → Prop) (h : P (l.reverse ++ [a])) :
    P (a :: l).reverse := by
  rw [List.reverse_cons]
  exact h

/-! ### R6. `List.append_assoc` · `as ++ bs ++ cs = as ++ (bs ++ cs)` · goal: regroup `++` to the right
`++` groups to the left: `l₁ ++ l₂ ++ l₃` is `(l₁ ++ l₂) ++ l₃`. -/
example {α : Type} (l₁ l₂ l₃ : List α) (P : List α → Prop) (h : P (l₁ ++ (l₂ ++ l₃))) :
    P (l₁ ++ l₂ ++ l₃) := by
  rw [List.append_assoc]
  exact h

/-! ### R7. `List.cons_append`, `List.nil_append` · goal: `[a] ++ l` → `a :: l`
`List.cons_append : a :: as ++ bs = a :: (as ++ bs)` (here `as = []`), then
`List.nil_append : [] ++ as = as`. `simp` uses exactly these two; `List.singleton_append :
[x] ++ l = x :: l` does both in one `rw`. -/
example {α : Type} (a : α) (l : List α) (P : List α → Prop) (h : P (a :: l)) : P ([a] ++ l) := by
  rw [List.cons_append]
  rw [List.nil_append]
  exact h

/-! ### R8. `List.append_nil` · `as ++ [] = as` · goal: drop an empty accumulator -/
example {α : Type} (l : List α) (P : List α → Prop) (h : P l) : P (l ++ []) := by
  rw [List.append_nil]
  exact h

/-! ## Indexing: `l[i]?` -/

/-! ### R9. `List.getElem?_reverse` · `i < l.length → l.reverse[i]? = l[l.length - 1 - i]?` · goal
`l[i]?` is the entry at position `i` (from 0) as an `Option`: `some x`, or `none` past the end.
The lemma needs `i < l.length`; pass it as the argument (`List.getElem?_reverse hi`), or `rw` adds
it as a side goal. `l.length - 1 - i` is `Nat` subtraction (cut off at 0). -/
example {α : Type} (l : List α) (i : Nat) (hi : i < l.length) (P : Option α → Prop)
    (h : P l[l.length - 1 - i]?) : P l.reverse[i]? := by
  rw [List.getElem?_reverse hi]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The accumulator lemma for `lenAcc`: R1, then R3 + R4 inside `simp`, then `omega`
The statement says what `lenAcc xs n` is for EVERY counter `n`, so the induction can carry it. -/
example {β : Type} (xs : List β) (n : Nat) : lenAcc xs n = xs.length + n := by
  induction xs generalizing n with
    | nil => simp [lenAcc]
    | cons y ys ih => simp [lenAcc, ih]; omega

/-! ### W2. The accumulator lemma for `dupAcc`: R1, R2, then `simp [dupAcc, ih]` (R3–R7 at once)
`List.flatMap f l` applies `f` to each element and concatenates the results:
`[1, 2].flatMap (fun x => [x, x]) = [1, 1, 2, 2]`. -/
example {β : Type} (xs acc : List β) :
    dupAcc xs acc = (xs.flatMap fun y => [y, y]).reverse ++ acc := by
  induction xs generalizing acc with
    | nil => rfl
    | cons y ys ih => simp [dupAcc, ih]

/-! ### W3. Using an accumulator lemma at `acc = []`: R4, then R8
With the lemma `hd` in hand (W2), the `acc = []` instance is one rewrite plus `List.append_nil`. -/
example {β : Type} (xs : List β)
    (hd : ∀ acc, dupAcc xs acc = (xs.flatMap fun y => [y, y]).reverse ++ acc) :
    dupAcc xs [] = (xs.flatMap fun y => [y, y]).reverse := by
  rw [hd]
  rw [List.append_nil]

end M016Guide

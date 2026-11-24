/- Guide for E082 (Arrays).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`pushZero`, one `push`).
Assumed: Lean basics (E001–E033).
-/

namespace E082Guide

/-! # Part R · Reference entries -/

/-! ## Array literals, `push`, `size` -/

/-! ### R1. `xs.push v` · appends `v` at the end; `rfl` closes a literal equation (goal closed)
`#[a, b]` is an array literal. `push` builds a new array; arrays are values, nothing is mutated. -/
example {α : Type} (a b c : α) : #[a, b].push c = #[a, b, c] := by
  rfl

/-! ### R2. `xs.size` of a literal · `rfl` closes it (goal closed): Lean counts the entries
`decide` works only when the entries are concrete, as in `#[1, 2, 3]`; here `a b` are variables. -/
example {α : Type} (a b : α) : #[a, b].size = 2 := by
  rfl

/-! ## `simp` with the `push` lemmas -/

/-! ### R3. `simp [f]` · goal: unfolds the definition `f`, then rewrites with `@[simp]` lemmas
Here `simp` uses R4 by itself. When the result is closed by `rfl` or arithmetic, `simp` closes the goal. -/
def pushZero (xs : Array Nat) : Array Nat := xs.push 0

example (xs : Array Nat) (P : Nat → Prop) (h : P (xs.size + 1)) : P (pushZero xs).size := by
  simp [pushZero]
  exact h

/-! ### R4. `Array.size_push` · `(xs.push v).size = xs.size + 1` · goal (a `@[simp]` lemma) -/
example {α : Type} (xs : Array α) (v : α) (P : Nat → Prop) (h : P (xs.size + 1)) :
    P (xs.push v).size := by
  rw [Array.size_push]
  exact h

/-! ### R5. `Array.toList_push` · `(xs.push x).toList = xs.toList ++ [x]` · goal (a `@[simp]` lemma) -/
example {α : Type} (xs : Array α) (v : α) (P : List α → Prop) (h : P (xs.toList ++ [v])) :
    P (xs.push v).toList := by
  rw [Array.toList_push]
  exact h

/-! ### R6. `List.append_assoc`, `List.cons_append`, `List.nil_append` · goal: `l ++ [u] ++ [v]` → `l ++ [u, v]`
`++` groups to the left; these three `@[simp]` lemmas regroup it and merge the singletons. -/
example {α : Type} (l : List α) (u v : α) (P : List α → Prop) (h : P (l ++ [u, v])) :
    P (l ++ [u] ++ [v]) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact h

/-! ## Reading an old index after `push` -/

/-! ### R7. `unfold f` · goal: the name `f` applied to arguments → `f`'s body -/
example (xs : Array Nat) (P : Array Nat → Prop) (h : P (xs.push 0)) : P (pushZero xs) := by
  unfold pushZero
  exact h

/-! ### R8. `Array.getElem?_push` · `(xs.push x)[i]? = if i = xs.size then some x else xs[i]?` · goal
`xs[i]?` is an `Option α`: `some` of the entry when `i < xs.size`, `none` otherwise. -/
example {α : Type} (xs : Array α) (v : α) (i : Nat) (P : Option α → Prop)
    (h : P (if i = xs.size then some v else xs[i]?)) : P (xs.push v)[i]? := by
  rw [Array.getElem?_push]
  exact h

/-! ### R9. `if_neg` · `(hnc : ¬c) : (if c then t else e) = e` · goal: take the `else` branch -/
example {α : Type} (c : Prop) [Decidable c] (t e : α) (hnc : ¬c) (P : α → Prop) (h : P e) :
    P (if c then t else e) := by
  rw [if_neg hnc]
  exact h

/-! ### R10. `simp` then `omega` · closes `¬i = (xs.push v).size` from `h : i < xs.size`
`omega` does not know what `push` does to the size: `simp` first rewrites it with R4.
In a `rw` write it in place: `if_neg (by simp; omega)`. -/
example {α : Type} (xs : Array α) (v : α) (i : Nat) (h : i < xs.size) : ¬i = (xs.push v).size := by
  simp
  omega

/-! ### R11. `Array.getElem?_eq_getElem` · `(h : i < xs.size) : xs[i]? = some xs[i]` · goal
`xs[i]` (no `?`) needs a proof of `i < xs.size`; Lean finds it in the context.
`exact Array.getElem?_eq_getElem hi` closes `⊢ xs[i]? = some xs[i]` directly. -/
example {α : Type} (xs : Array α) (i : Nat) (hi : i < xs.size) (P : Option α → Prop)
    (h : P (some xs[i])) : P xs[i]? := by
  rw [Array.getElem?_eq_getElem hi]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `simp [f]` closes size and list facts about a one-`push` function (R3, R4, R5) -/
example (xs : Array Nat) : (pushZero xs).size = xs.size + 1 := by
  simp [pushZero]

example (xs : Array Nat) : (pushZero xs).toList = xs.toList ++ [0] := by
  simp [pushZero]

/-! ### W2. An old index survives one `push`: R7, R8, R9 with `omega`, R11 -/
example (xs : Array Nat) (i : Nat) (h : i < xs.size) : (pushZero xs)[i]? = some xs[i] := by
  unfold pushZero
  rw [Array.getElem?_push]
  rw [if_neg (by omega)]
  exact Array.getElem?_eq_getElem h

/-! ### W3. The new index: the `if` is true, so use `if_pos` (the mirror of R9) -/
example (xs : Array Nat) (v : Nat) : (xs.push v)[xs.size]? = some v := by
  rw [Array.getElem?_push]
  rw [if_pos rfl]

end E082Guide

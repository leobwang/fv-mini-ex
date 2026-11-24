/- Guide for E059 (Indexing lists).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`headOr`, other lists).
Assumed: Lean basics (E001–E033).
-/

namespace E059Guide

/-! # Part R · Reference entries -/

/-! ## Building a value with a dependent `if` -/

/-! ### R1. `if h : c then … else …` · goal list: one goal per branch, context gains `h : c` / `h : ¬c`
In a definition you write it as a term; `refine` with `?_` in each branch shows what each branch sees. -/
example {α : Type} (xs : List α) (d : α) : α := by
  refine if h : 0 < xs.length then ?_ else ?_
  exact xs[0]
  exact d

/-! ### R2. `xs[n]` · `exact xs[n]` closes `⊢ α` when `h : n < xs.length` is in the context
The bound `n < xs.length` is proved automatically (by `get_elem_tactic`), using hypotheses. -/
example {α : Type} (xs : List α) (n : Nat) (h : n < xs.length) : α := by
  exact xs[n]

/-! ## Looking up a literal list -/

/-! ### R3. `rfl` on `[a, b, c][k]` · closes the goal (Lean evaluates the lookup)
On a literal list the bound `k < 3` is proved automatically too. -/
example : [5, 6, 7][2] = 7 := by
  rfl

/-! ### R4. `xs[k]?` is an `Option α`: `some xᵢ` in range, `none` out of range · `rfl` closes it -/
example : [5, 6, 7][2]? = some 7 ∧ [5, 6, 7][9]? = none := by
  exact ⟨rfl, rfl⟩

/-! ## Unfolding a definition and picking a branch -/

/-! ### R5. `unfold f` · goal: the name `f` applied to arguments → `f`'s body -/
def headOr {α : Type} (xs : List α) (d : α) : α :=
  if h : 0 < xs.length then xs[0] else d

example {α : Type} (xs : List α) (d : α) (P : α → Prop)
    (h : P (if h : 0 < xs.length then xs[0] else d)) : P (headOr xs d) := by
  unfold headOr
  exact h

/-! ### R6. `dif_pos` · `(hc : c) : (if h : c then t h else e h) = t hc` · goal: take the `then` branch -/
example {α : Type} (c : Prop) [Decidable c] (t : c → α) (e : ¬c → α) (hc : c) (P : α → Prop)
    (h : P (t hc)) : P (if h : c then t h else e h) := by
  rw [dif_pos hc]
  exact h

/-! ### R7. `dif_neg` · `(hnc : ¬c) : (if h : c then t h else e h) = e hnc` · goal: take the `else` branch -/
example {α : Type} (c : Prop) [Decidable c] (t : c → α) (e : ¬c → α) (hnc : ¬c) (P : α → Prop)
    (h : P (e hnc)) : P (if h : c then t h else e h) := by
  rw [dif_neg hnc]
  exact h

/-! ### R8. `omega` proves `¬ n < m` from `m ≤ n` · closes the goal
Use it in place as an argument: `dif_neg (by omega)`. -/
example (n m : Nat) (h : m ≤ n) : ¬ n < m := by
  omega

/-! ## `xs[n]?` versus `xs[n]` -/

/-! ### R9. `List.getElem?_eq_getElem` · `(h : i < l.length) : l[i]? = some l[i]` · goal
`exact List.getElem?_eq_getElem h` closes `⊢ xs[n]? = some xs[n]` directly. -/
example {α : Type} (xs : List α) (n : Nat) (hn : n < xs.length) (P : Option α → Prop)
    (h : P (some xs[n])) : P xs[n]? := by
  rw [List.getElem?_eq_getElem hn]
  exact h

/-! ## Indexing a mapped list -/

/-! ### R10. `xs[n]'p` · you give the bound proof `p` yourself; `'?_` makes it a goal -/
example {α β : Type} (f : α → β) (xs : List α) (n : Nat) (hn : n < xs.length) : β := by
  refine (xs.map f)[n]'?_
  simpa using hn

/-! ### R11. `simpa using hn` · closes `⊢ n < (List.map f xs).length` from `hn : n < xs.length`
`simp` rewrites the goal with `List.length_map : (List.map f as).length = as.length`, then `hn` closes it. -/
example {α β : Type} (f : α → β) (xs : List α) (n : Nat) (hn : n < xs.length) :
    n < (xs.map f).length := by
  simpa using hn

/-! ### R12. `List.getElem_map` · `(f : α → β) : (List.map f l)[i] = f l[i]` · goal
The bound proof of `(List.map f l)[i]` is an implicit argument: Lean finds it. -/
example {α β : Type} (f : α → β) (xs : List α) (n : Nat) (hn : n < (xs.map f).length)
    (P : β → Prop) (h : P (f (xs[n]'(by simpa using hn)))) : P ((xs.map f)[n]) := by
  rw [List.getElem_map]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `unfold` then `dif_pos` (R5, R6) -/
theorem headOr_pos {α : Type} (xs : List α) (d : α) (h : 0 < xs.length) : headOr xs d = xs[0] := by
  unfold headOr
  rw [dif_pos h]

/-! ### W2. `unfold` then `dif_neg (by omega)` (R5, R7, R8) -/
example {α : Type} (xs : List α) (d : α) (h : xs.length = 0) : headOr xs d = d := by
  unfold headOr
  rw [dif_neg (by omega)]

/-! ### W3. Rewrite with an earlier theorem (W1), then R9 -/
example {α : Type} (xs : List α) (d : α) (h : 0 < xs.length) : xs[0]? = some (headOr xs d) := by
  rw [headOr_pos xs d h]
  exact List.getElem?_eq_getElem h

/-! ### W4. A mapped lookup closed by the lemma as a term (R12)
`List.getElem_map _` proves `… = (· + 1) xs[n]`, which Lean accepts as `… = xs[n] + 1` (β-reduction). -/
example (xs : List Nat) (n : Nat) (h : n < xs.length) :
    (xs.map (· + 1))[n]'(by simpa using h) = xs[n] + 1 :=
  List.getElem_map _

end E059Guide

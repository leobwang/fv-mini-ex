/- Guide for M037 (Rose trees: nested inductives).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own nested inductive, which is NOT the exercise's: `Bush α`, a tree whose
node holds a label `a : α` and a list `kids` of subtrees, with `Bush.count` (number of nodes) and
`Bush.map` (apply a function to every label).
Part W: worked combinations on `Bush` (functor laws for `Bush.map`, `count` of a mapped tree).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M037Guide

/-- A nested inductive: the recursive occurrence `Bush α` sits inside another type, `List`. -/
inductive Bush (α : Type) where
  | br (a : α) (kids : List (Bush α))

/-- Number of nodes. The recursive call goes through `List.map`; Lean accepts it by well-founded
recursion (each `k ∈ kids` is smaller than `.br a kids`), not by structural recursion. -/
def Bush.count {α : Type} : Bush α → Nat
  | .br _ kids => 1 + (kids.map Bush.count).sum

/-- Apply `f` to every label, keeping the shape. -/
def Bush.map {α β : Type} (f : α → β) : Bush α → Bush β
  | .br a kids => .br (f a) (kids.map (Bush.map f))

/-! # Part R · Reference entries -/

/-! ## Recursion on a nested inductive -/

/-! ### R1. `match t with | .br a kids => ?_` · context gains the fields `a`, `kids`; goal: `t` → `.br a kids`
`induction t` and `induction t with` reject a nested inductive. `match` splits by constructor
instead (here one constructor, so one goal). `t` itself stays in the context, unused. -/
example {α : Type} (P : Bush α → Prop) (h : ∀ a kids, P (.br a kids)) (t : Bush α) : P t := by
  match t with | .br a kids => ?_
  exact h a kids

/-! ### R2. Recursive theorem: `have ih : ∀ k ∈ kids, P k := fun k _ => thm … k` · context gains `ih`
The theorem calls itself on each child: that call IS the induction hypothesis. Lean then proves
termination: from the membership proof (the `_`) it derives `sizeOf k < sizeOf (.br a kids)`. A
`have ih : ∀ k, P k` (no `∈ kids`) fails that check. `bush_all` is the induction principle for
`Bush` that `induction` would have given. -/
theorem bush_all {α : Type} (P : Bush α → Prop)
    (step : ∀ a kids, (∀ k ∈ kids, P k) → P (.br a kids)) (t : Bush α) : P t := by
  match t with | .br a kids => ?_
  have ih : ∀ k ∈ kids, P k := fun k _ => bush_all P step k
  exact step a kids ih

/-! ### R3. `simp only [Bush.count]` · goal: a definition on a constructor → its clause
`Bush.count` is defined by well-founded recursion, so `rfl` and `decide` cannot unfold it; `simp only`
(or `rw`) uses the equation lemma Lean generated for the clause. -/
example {α : Type} (a : α) (kids : List (Bush α)) (P : Nat → Prop)
    (h : P (1 + (kids.map Bush.count).sum)) : P (Bush.br a kids).count := by
  simp only [Bush.count]
  exact h

/-! ## Lengths and sums -/

/-! ### R4. `List.length_cons` · `(a :: as).length = as.length + 1` · goal -/
example {α : Type} (a : α) (as : List α) (P : Nat → Prop) (h : P (as.length + 1)) :
    P (a :: as).length := by
  rw [List.length_cons]
  exact h

/-! ### R5. `List.length_flatten` · `L.flatten.length = (L.map List.length).sum` · goal
`L.flatten` concatenates a list of lists, so its length is the sum of the lengths. -/
example {α : Type} (L : List (List α)) (P : Nat → Prop) (h : P (L.map List.length).sum) :
    P L.flatten.length := by
  rw [List.length_flatten]
  exact h

/-! ## Maps -/

/-! ### R6. `List.map_map` · `(l.map u).map v = l.map (v ∘ u)` · goal: two maps → one map -/
example {α β γ : Type} (u : α → β) (v : β → γ) (l : List α) (P : List γ → Prop)
    (h : P (l.map (v ∘ u))) : P ((l.map u).map v) := by
  rw [List.map_map]
  exact h

/-! ### R7. `List.map_congr_left` · `(∀ a ∈ l, f a = g a) → l.map f = l.map g` · goal
This turns the induction hypothesis into an equation of maps. Name `f` and `g`: from `hvu` alone Lean
would guess `f := fun a => v (u a)`, which is not literally the `v ∘ u` in the goal, so `rw` finds
nothing. -/
example {α β γ : Type} (u : α → β) (v : β → γ) (w : α → γ) (l : List α)
    (hvu : ∀ a ∈ l, v (u a) = w a) (P : List γ → Prop) (h : P (l.map w)) :
    P (l.map (v ∘ u)) := by
  rw [List.map_congr_left (f := v ∘ u) (g := w) hvu]
  exact h

/-! ### R8. `omega` · closes linear arithmetic over `Nat`/`Int`; other subterms count as atoms -/
example {α : Type} (u : α → Nat) (l : List α) : (l.map u).sum + 1 = 1 + (l.map u).sum := by omega

/-! ## Reversal -/

/-! ### R9. `List.map_reverse` · `l.reverse.map u = (l.map u).reverse` · goal: map moves inside -/
example {α β : Type} (u : α → β) (l : List α) (P : List β → Prop) (h : P (l.map u).reverse) :
    P (l.reverse.map u) := by
  rw [List.map_reverse]
  exact h

/-! ### R10. `List.sum_reverse` · `l.reverse.sum = l.sum` · goal (for `Nat`, and any `+` that is
associative and commutative with `0` as unit) -/
example (l : List Nat) (P : Nat → Prop) (h : P l.sum) : P l.reverse.sum := by
  rw [List.sum_reverse]
  exact h

/-! ### R11. `List.reverse_reverse` · `l.reverse.reverse = l` · goal -/
example {α : Type} (l : List α) (P : List α → Prop) (h : P l) : P l.reverse.reverse := by
  rw [List.reverse_reverse]
  exact h

/-! ### R12. `List.map_id` · `l.map id = l` · goal (`id` is the identity function `fun x => x`) -/
example {α : Type} (l : List α) (P : List α → Prop) (h : P l) : P (l.map id) := by
  rw [List.map_id]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Functor law `t.map id = t`: R1, R2, unfold, R7 (with `g := id`), R12
`rw` tries `rfl` only up to reducible unfolding and leaves `Bush.br (id a) kids = Bush.br a kids`;
a plain `rfl` unfolds `id a` to `a` and closes it. -/
theorem bush_map_id {α : Type} (t : Bush α) : t.map id = t := by
  match t with | .br a kids => ?_
  have ih : ∀ k ∈ kids, k.map id = k := fun k _ => bush_map_id k
  simp only [Bush.map]
  rw [List.map_congr_left (f := Bush.map id) (g := id) ih]
  rw [List.map_id]
  rfl

/-! ### W2. Mapping keeps the node count: R1, R2, R3, R6, R7 -/
theorem bush_count_map {α β : Type} (f : α → β) (t : Bush α) : (t.map f).count = t.count := by
  match t with | .br a kids => ?_
  have ih : ∀ k ∈ kids, (k.map f).count = k.count := fun k _ => bush_count_map f k
  simp only [Bush.map, Bush.count]
  rw [List.map_map]
  rw [List.map_congr_left (f := Bush.count ∘ Bush.map f) (g := Bush.count) ih]

end M037Guide

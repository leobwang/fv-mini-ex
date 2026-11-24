/- Guide for M035 (Iterative in-order traversal).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own objects, which are NOT the exercise's: a polymorphic tree `BT α`,
`pushAll` (structural recursion: move a list onto a stack), `flat` (well-founded recursion: flatten a
stack of lists one element at a time) and `pre` (pre-order list of a `BT`).
Part W: worked combinations on `flat` and `pushAll`.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M035Guide

/-- A binary tree whose nodes carry a value of any type `α`. -/
inductive BT (α : Type) where
  | tip
  | fork (l : BT α) (a : α) (r : BT α)

/-- Structural recursion: each call is on the tail `xs`, a piece of the argument `x :: xs`. -/
def pushAll {α : Type} : List α → List α → List α
  | [], s => s
  | x :: xs, s => pushAll xs (x :: s)

/-- Well-founded recursion: `xs :: rest` is not a piece of `(x :: xs) :: rest`, so Lean needs the
measure after `termination_by` (one unit per list plus one per element) and a proof that it drops. -/
def flat : List (List Nat) → List Nat
  | [] => []
  | [] :: rest => flat rest
  | (x :: xs) :: rest => x :: flat (xs :: rest)
termination_by l => (l.map (fun p => p.length + 1)).sum
decreasing_by all_goals simp

/-- Pre-order: the root first, then the left subtree, then the right subtree. -/
def pre {α : Type} : BT α → List α
  | .tip => []
  | .fork l a r => a :: (pre l ++ pre r)

/-! # Part R · Reference entries -/

/-! ## The helper lemma: induction with the stack generalised -/

/-! ### R1. `induction t generalizing s with | tip => … | fork l a r ihl ihr => …` · goal list, context
One goal per constructor. `generalizing s` takes `s` out of the context first, so each induction
hypothesis holds for EVERY `s`: `ihl : ∀ (s : σ), P l s`. Arms `?_` keep both goals open to show them. -/
example {α σ : Type} (P : BT α → σ → Prop) (h0 : ∀ s, P .tip s)
    (h1 : ∀ l a r, (∀ s, P l s) → (∀ s, P r s) → ∀ s, P (.fork l a r) s) (t : BT α) (s : σ) :
    P t s := by
  induction t generalizing s with | tip => ?_ | fork l a r ihl ihr => ?_
  · exact h0 s
  · exact h1 l a r ihl ihr s

/-! ### R2. `rfl` · closes a goal that holds by unfolding STRUCTURAL definitions
`pushAll [] s` unfolds to `s`, and `[] ++ m` unfolds to `m`, so both sides are the same term.
(It does not unfold a well-founded definition such as `flat`: see R5, R9.) -/
example {α β : Type} (g : List α → List β) (s : List α) : g (pushAll [] s) = [] ++ g s := by
  rfl

/-! ### R3. `rw [pushAll]` · goal: a structural definition on a constructor → that clause, once -/
example {α : Type} (x : α) (xs s : List α) (P : List α → Prop) (h : P (pushAll xs (x :: s))) :
    P (pushAll (x :: xs) s) := by
  rw [pushAll]
  exact h

/-! ### R4. `rw [ih]` with `ih : ∀ s, F s = G s` · goal: `F e` → `G e`, the `∀` filled in by matching
`rw` finds the instance `s := c s₀` itself. The same works for a helper theorem you proved earlier. -/
example {σ β : Type} (F G : σ → β) (c : σ → σ) (ih : ∀ s, F s = G s) (s₀ : σ) (P : β → Prop)
    (h : P (G (c s₀))) : P (F (c s₀)) := by
  rw [ih]
  exact h

/-! ### R5. `rw [flat]` on a WELL-FOUNDED definition · goal: one clause applied, via its equation lemma
Lean proves equations `flat.eq_1`, `flat.eq_2`, `flat.eq_3` (one per clause); `rw [flat]` uses the one
that matches. `rfl` and `decide` cannot do this step. -/
example (x : Nat) (xs : List Nat) (rest : List (List Nat)) (P : List Nat → Prop)
    (h : P (x :: flat (xs :: rest))) : P (flat ((x :: xs) :: rest)) := by
  rw [flat]
  exact h

/-! ## Closing a list equation -/

/-! ### R6. `List.append_assoc` · `as ++ bs ++ cs = as ++ (bs ++ cs)` · goal (`++` groups to the left) -/
example {α : Type} (as bs cs : List α) (P : List α → Prop) (h : P (as ++ (bs ++ cs))) :
    P (as ++ bs ++ cs) := by
  rw [List.append_assoc]
  exact h

/-! ### R7. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (h : P (a :: (as ++ bs))) :
    P (a :: as ++ bs) := by
  rw [List.cons_append]
  exact h

/-! ### R8. `simp [d]` · closes: unfold `d` on a constructor, then R6 and R7 (simp lemmas) by itself -/
example {α : Type} (l r : BT α) (a : α) (s : List α) :
    a :: (pre l ++ (pre r ++ s)) = pre (.fork l a r) ++ s := by
  simp [pre]

/-! ## The main theorem from the helper -/

/-! ### R9. `rw [flat]` on the empty stack · goal: `flat []` → `[]` (equation lemma `flat.eq_1`)
Also a well-founded definition: `rfl` fails here, `rw`/`simp [flat]` work. -/
example (P : List Nat → Prop) (h : P []) : P (flat []) := by
  rw [flat]
  exact h

/-! ### R10. `List.append_nil` · `as ++ [] = as` · goal -/
example {α : Type} (as : List α) (P : List α → Prop) (h : P as) : P (as ++ []) := by
  rw [List.append_nil]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A stack whose top list is pushed in front: `flat (m :: rest) = m ++ flat rest`
`rest` never changes in the recursion on `m`, so no `generalizing` is needed. R5, R2, R4, R7.
Each tactic below works on the first open goal: `nil` first, then `cons`. -/
example (m : List Nat) (rest : List (List Nat)) : flat (m :: rest) = m ++ flat rest := by
  induction m with | nil => ?_ | cons x xs ih => ?_
  rw [flat]
  rfl
  rw [flat]
  rw [ih]
  rw [List.cons_append]

/-! ### W2. An accumulator that grows: `pushAll xs s = xs.reverse ++ s` needs `generalizing s`
The recursive call is at `x :: s`, not `s`, so `ih` must hold for every stack. R1, R2, R3, R4, then
`simp` (with `List.reverse_cons : (a :: as).reverse = as.reverse ++ [a]` and R6). -/
example {α : Type} (xs s : List α) : pushAll xs s = xs.reverse ++ s := by
  induction xs generalizing s with | nil => ?_ | cons x xs ih => ?_
  rfl
  rw [pushAll]
  rw [ih]
  simp

/-! ### W3. Evaluating `flat` on a literal: `simp [flat]` applies the equation lemmas repeatedly -/
example : flat [[1, 2], [], [3]] = [1, 2, 3] := by
  simp [flat]

end M035Guide

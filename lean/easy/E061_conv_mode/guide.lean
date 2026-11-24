/- Guide for E061 (conv mode).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of a statement": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Inside a `conv` block the infoview shows a CONV GOAL `| e` instead of `⊢ G`: `e` is the subterm you
are focused on. Put the cursor after each line of the block to watch the focus move.
Part W: worked combinations on terms that are NOT the exercise's (`* 1` instead of `0 +`).
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace E061Guide

/-! # Part R · Reference entries -/

/-! ## Entering and leaving conv mode -/

/-! ### R1. `conv => tacs` · goal: rewritten by the conv tactics `tacs`
Inside the block the goal `⊢ G` is a conv goal `| G`; conv tactics move the focus or rewrite the
focused term. When the block ends, `G` is replaced by the rewritten term. -/
example {α : Type} (a b : α) (P : α → Prop) (e : a = b) (h : P b) : P a := by
  conv =>
    rw [e]
  exact h

/-! ### R2. `lhs` / `rhs` (conv) · focus: `| a = b` → `| a` (`rhs`: → `| b`)
Navigation alone changes nothing: the block ends with the goal as it was. -/
example {α : Type} (a b : α) (e : a = b) : a = b := by
  conv =>
    lhs
  exact e

/-! ### R3. `intro x` (conv) · focus: `| fun x => t x` → `| t x`, with a new local `x` in the context
Under a binder the bound variable is not a term `rw` can name. `intro x` makes it a local `x : α`,
so the body can be rewritten like any other term. (When the block ends, Lean rebuilds the
`fun x => …` and eta-reduces `fun x => t x` to `t`: the goal is `t = u`, see R5.) -/
example {α β : Type} (t u : α → β) (h : t = u) : (fun x => t x) = u := by
  conv =>
    lhs
    intro x
  exact h

/-! ### R4. `Nat.zero_add` · `Nat.zero_add (n : Nat) : 0 + n = n` · goal: `0 + n` → `n`
`0 + n` does not compute to `n` (`+` recurses on its SECOND argument), so a lemma is needed.
Inside conv, `rw [Nat.zero_add]` rewrites the focused term the same way. -/
example (P : Nat → Prop) (n : Nat) (h : P n) : P (0 + n) := by
  rw [Nat.zero_add]
  exact h

/-! ### R5. End of a `conv` block · goal list: Lean tries `rfl` on the new goal and closes it if it can
The new goal is rebuilt from the focus, with `fun x => t x` eta-reduced to `t`. The `rfl` runs at
reducible transparency (`with_reducible rfl`): it does not unfold ordinary definitions such as
`List.map`, so `List.map (fun x => x) xs = xs` stays open. -/
example {α : Type} (a b : α) (e : a = b) : a = b := by
  conv =>
    rw [e]

example {α β : Type} (t : α → β) : (fun x => t x) = t := by
  conv =>
    lhs
    intro x

/-! ## Moving the focus into arguments -/

/-! ### R6. `arg i` (conv) · focus: `| F a₁ … aₙ` → `| aᵢ`, the i-th EXPLICIT argument, counted from 1
`List.map t xs` has explicit arguments `t` (`arg 1`) and `xs` (`arg 2`); its type arguments are
implicit and skipped (`arg @i` counts them too). -/
example {α β : Type} (t : α → β) (xs : List α) (ys : List β) (h : List.map t xs = ys) :
    List.map t xs = ys := by
  conv =>
    lhs
    arg 1
  exact h

/-! ### R7. `List.map_id'` · `List.map_id' (l : List α) : List.map (fun a => a) l = l` · closes the goal
Mapping the identity function changes nothing. It is not `rfl` for a variable list `l`, so name it.
(`List.map_id` is the same fact for `id` instead of `fun a => a`.) -/
example {α : Type} (l : List α) : List.map (fun a => a) l = l := by
  exact List.map_id' l

/-! ## Other places to start -/

/-! ### R8. `conv at h => tacs` · context: hypothesis `h` rewritten; goal unchanged
The conv goal starts as `| (type of h)`. No `rfl` is tried at the end (`h` is not a goal). -/
example {α : Type} (a b : α) (P : α → Prop) (e : a = b) (h : P a) : P b := by
  conv at h =>
    rw [e]
  exact h

/-! ### R9. `conv in pat => tacs` · goal: focus jumps to the first subterm matching `pat`, even under a binder
`_` in `pat` matches anything, including the bound variable; that variable becomes a local `x`. -/
example {α β : Type} (g : α → α → β) (a b : α) (e : ∀ x, g x a = g x b) (P : (α → β) → Prop)
    (h : P (fun x => g x b)) : P (fun x => g x a) := by
  conv in g _ a =>
    rw [e]
  exact h

/-! # Part W · Worked combinations (not the exercise's terms) -/

/-! ### W1. Under a binder in the goal: R1, R2, R3, then `rw` with `Nat.mul_one : n * 1 = n`; R5 closes -/
example (g : Nat → Nat) : (fun x => g (x * 1)) = g := by
  conv =>
    lhs
    intro x
    rw [Nat.mul_one]

/-! ### W2. In a hypothesis, two levels down: R8, `rhs`, R6, then `exact` -/
example (a b c : Nat) (h : a = b * (c * 1)) : a = b * c := by
  conv at h =>
    rhs
    arg 2
    rw [Nat.mul_one]
  exact h

/-! ### W3. Related, not conv: `rw (occs := [k])` rewrites only the k-th match (here the first) -/
example (a b : Nat) : a + b + (a + b) = b + a + (a + b) := by
  rw (occs := [1]) [Nat.add_comm a b]

end E061Guide

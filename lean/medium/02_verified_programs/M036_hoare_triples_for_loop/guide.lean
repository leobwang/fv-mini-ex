/- Guide for M036 (Hoare triples for a for-loop, mvcgen warm-up).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The `mvcgen` entries need a concrete program, so they use small programs that are NOT the exercise's
(`clampLo` raises a number to a floor, `sumBig` sums the elements above a threshold).
Part W: worked combinations on another program (the sum of a list).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean and `Std.Do`.
-/
import Std.Tactic.Do
open Std.Do
set_option mvcgen.warning false

namespace M036Guide

/-! # Part R · Reference entries -/

/-! ## Hoare triples and `mvcgen` -/

/-! ### R1. `mvcgen [f]` · goal: a Hoare triple → its verification conditions (plain `Prop` goals)
`⦃⌜True⌝⦄ prog ⦃⇓ r => ⌜Q r⌝⦄`: run from any state, `prog` returns some `r` with `Q r`. `⌜p⌝` turns
the `Prop` `p` into an assertion; `⇓ r => …` prints as `PostCond.noThrow fun r => …`. `mvcgen [f]`
unfolds `f` and walks through the program; an `if` gives one goal per branch (`isTrue`, `isFalse`)
with the branch condition as a hypothesis `h✝`. -/
def clampLo (t n : Nat) : Id Nat := do
  let mut a := n
  if a < t then
    a := t
  return a

example (t n : Nat) : ⦃⌜True⌝⦄ clampLo t n ⦃⇓ r => ⌜t ≤ r⌝⦄ := by
  mvcgen [clampLo]
  all_goals grind

/-! ### R2. `List.Cursor` · a split `xs = cur.prefix ++ cur.suffix` of the list being looped over
`cur.prefix` is the part already processed, `cur.suffix` the part still to go. In a loop VC the
current element sits between them: `xs = pref✝ ++ cur✝ :: suff✝`, and the goal is about
`pref✝ ++ [cur✝]`. -/
example (xs : List Nat) (cur : xs.Cursor) : cur.prefix ++ cur.suffix = xs := cur.property

/-! ### R3. `mvcgen [f] invariants · ⇓⟨cur, s⟩ => ⌜I⌝` · goal → one VC per loop-body branch, plus `pre`
The invariant is a postcondition on the pair (cursor, current value of the `let mut`). Write the `·`
line right after `mvcgen … invariants`, at the same column or indented further. The VCs: each branch of the body keeps `I` (`step.isTrue`,
`step.isFalse`), `I` holds at entry with `cur.prefix = []` (`pre`), and `I` with `cur.prefix = xs`
gives the postcondition (`post.success`; `mvcgen` closes it itself when it is immediate). -/
def sumBig (t : Nat) (l : List Nat) : Id Nat := do
  let mut s := 0
  for x in l do
    if t < x then
      s := s + x
  return s

example (t : Nat) (xs : List Nat) : ⦃⌜True⌝⦄ sumBig t xs ⦃⇓ r => ⌜r ≤ xs.sum⌝⦄ := by
  mvcgen [sumBig] invariants
    · ⇓⟨cur, s⟩ => ⌜s ≤ cur.prefix.sum⌝
  all_goals grind

/-! ## Closing the VCs: membership in `pref ++ [c]` (`grind` uses these by itself) -/

/-! ### R4. `List.mem_append` · `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` · goal -/
example {α : Type} (a : α) (s t : List α) (P : Prop → Prop) (h : P (a ∈ s ∨ a ∈ t)) :
    P (a ∈ s ++ t) := by
  rw [List.mem_append]
  exact h

/-! ### R5. `List.mem_singleton` · `a ∈ [b] ↔ a = b` · goal -/
example {α : Type} (a b : α) (P : Prop → Prop) (h : P (a = b)) : P (a ∈ [b]) := by
  rw [List.mem_singleton]
  exact h

/-! ### R6. `List.mem_nil_iff` · `a ∈ [] ↔ False` · goal: the entry VC talks about `[]` -/
example {α : Type} (a : α) (P : Prop → Prop) (h : P False) : P (a ∈ ([] : List α)) := by
  rw [List.mem_nil_iff]
  exact h

/-! ### R7. `grind` · closes the goal
It combines linear arithmetic over `Nat` (`+`, `<`, `≤`, numerals), splitting `∧`, `∨` and `if`,
instantiating `∀` hypotheses at the terms it sees, and rewriting with lemmas tagged for it, R4–R6
included. So every VC of a small loop is one `grind`; `all_goals grind` closes them all. -/
example (p : List Nat) (b c : Nat) (h : ∀ y, y ∈ p → y < b) (hb : b ≤ c) :
    ∀ y, y ∈ p ++ [c] → y ≤ c := by
  grind

example (p : List Nat) (a c : Nat) (h : a ∈ p ∨ a = c) : a ∈ p ++ [c] := by
  grind

/-! ## From a triple to a fact about `.run` -/

/-! ### R8. `Id.of_wp_run_eq` · `prog.run = x → ∀ P, (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) → P x` · context
`prog.run` is the value an `Id` program computes. With `x := prog.run` (proved by `rfl`), the lemma
turns "`P` holds after `prog`" (`⊢ₛ wp⟦prog⟧ …`, a weakest precondition) into `P prog.run`. -/
example {α : Type} (prog : Id α) (P : α → Prop) (hw : ⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) (G : Prop)
    (g : P prog.run → G) : G := by
  have h := Id.of_wp_run_eq rfl P hw
  exact g h

/-! ### R9. A triple `⦃⌜True⌝⦄ prog ⦃⇓ a => ⌜P a⌝⦄` is the `wp` argument of R8 · context
By definition the triple is `⌜True⌝ ⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)`, so pass it as the third argument.
Write `_` for `P`: Lean reads `P` off the triple's postcondition. -/
example {α : Type} (prog : Id α) (P : α → Prop) (ht : ⦃⌜True⌝⦄ prog ⦃⇓ a => ⌜P a⌝⦄) (G : Prop)
    (g : P prog.run → G) : G := by
  have h := Id.of_wp_run_eq rfl _ ht
  exact g h

/-! ### R10. `h.1` (`And.left`) · context: from `h : A ∧ B` take `A` (`h.2` takes `B`) -/
example (A B G : Prop) (h : A ∧ B) (g : A → G) : G := by
  have hA := h.1
  exact g hA

/-! ### R11. `h x hx` · context: instantiate a bounded `∀`
`∀ x ∈ xs, Q x` is notation for `∀ x, x ∈ xs → Q x` and prints as `∀ (x : α), x ∈ xs → Q x`: a function
taking `x` and a membership proof. -/
example {α : Type} (xs : List α) (Q : α → Prop) (h : ∀ x ∈ xs, Q x) (x : α) (hx : x ∈ xs) (G : Prop)
    (g : Q x → G) : G := by
  have hq := h x hx
  exact g hq

/-! # Part W · Worked combinations (not the exercise's program) -/

/-! ### W1. Invariant = postcondition with `xs` replaced by `cur.prefix`, then `all_goals grind`
`sumL` sums a list; every element is at most the sum. -/
def sumL (l : List Nat) : Id Nat := do
  let mut s := 0
  for x in l do
    s := s + x
  return s

theorem sumL_bound (xs : List Nat) : ⦃⌜True⌝⦄ sumL xs ⦃⇓ r => ⌜∀ y ∈ xs, y ≤ r⌝⦄ := by
  mvcgen [sumL] invariants
    · ⇓⟨cur, s⟩ => ⌜∀ y ∈ cur.prefix, y ≤ s⌝
  all_goals grind

/-! ### W2. Term mode: R9, then R11 on the result (no `by` needed) -/
example (xs : List Nat) (y : Nat) (hy : y ∈ xs) : y ≤ (sumL xs).run :=
  Id.of_wp_run_eq rfl _ (sumL_bound xs) y hy

end M036Guide

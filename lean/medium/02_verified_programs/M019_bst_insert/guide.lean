/- Guide for M019 (BST insert).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G` is a
goal the step does not touch. A hypothesis `h`/`g` in an entry is only there to finish the example.
Part W: worked combinations on objects that are NOT the exercise's (a tree `BT`, `mirror`, `prune`,
a max-heap predicate `Heap`).
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M019Guide

/-- A binary tree with `Nat` labels (the guide's own, not the exercise's `Tree`). -/
inductive BT where
  | tip
  | bin (l : BT) (a : Nat) (r : BT)

/-- `has y t`: the label `y` occurs in `t` (root first). A recursive function into `Prop`. -/
def has (y : Nat) : BT → Prop
  | .tip => False
  | .bin l a r => y = a ∨ has y l ∨ has y r

/-- `every p t`: every label of `t` satisfies `p` (root first). -/
def every (p : Nat → Prop) : BT → Prop
  | .tip => True
  | .bin l a r => p a ∧ every p l ∧ every p r

/-- Swap left and right everywhere. -/
def mirror : BT → BT
  | .tip => .tip
  | .bin l a r => .bin (mirror r) a (mirror l)

/-- Drop every node whose label is below `x`, together with its left subtree. -/
def prune (x : Nat) : BT → BT
  | .tip => .tip
  | .bin l a r => if a < x then prune x r else .bin (prune x l) a r

/-- Max-heap: every label is `≤` the label of its parent. An inductive predicate. -/
inductive Heap : BT → Prop
  | tip : Heap .tip
  | bin {l : BT} {a : Nat} {r : BT} :
      every (· ≤ a) l → every (· ≤ a) r → Heap l → Heap r → Heap (.bin l a r)

/-! # Part R · Reference entries -/

/-! ## Recursion over a tree -/

/-! ### R1. `induction t with | tip => ?_ | bin l a r ihl ihr => ?_` · goal list; context gains `ihl ihr`
One goal per constructor. For `bin`, the induction hypotheses `ihl`, `ihr` are the goal for the
subtrees `l` and `r`. `?_` leaves each goal open for the next tactics. -/
example (P : BT → Prop) (t : BT) (h0 : P .tip) (h1 : ∀ l a r, P l → P r → P (.bin l a r)) :
    P t := by
  induction t with
    | tip => ?_
    | bin l a r ihl ihr => ?_
  exact h0
  exact h1 l a r ihl ihr

/-! A hypothesis about `t` in the context (`ht : Q t`) is carried along: the induction hypotheses
become implications `Q l → P l`, and `ht` is about `bin l a r` in the `bin` goal. -/
example (P Q : BT → Prop) (t : BT) (ht : Q t) (h0 : Q .tip → P .tip)
    (h1 : ∀ l a r, (Q l → P l) → (Q r → P r) → Q (.bin l a r) → P (.bin l a r)) : P t := by
  induction t with
    | tip => ?_
    | bin l a r ihl ihr => ?_
  exact h0 ht
  exact h1 l a r ihl ihr ht

/-! ### R2. `simp only [f]` · goal: a recursive function applied to a constructor → that arm
`has y (bin l a r)` is replaced by the `bin` arm of `has`. A call on a non-constructor such as
`has y (prune x l)` stays: Lean does not know which arm applies. -/
example (y a : Nat) (l r : BT) (P : Prop → Prop) (h : P (y = a ∨ has y l ∨ has y r)) :
    P (has y (.bin l a r)) := by
  simp only [has]
  exact h

/-! ### R3. `unfold f` · goal: one call `f x (bin l a r)` → the body of its `bin` arm, `if` included
The recursive calls inside the body (`prune x r`, `prune x l`) stay folded. -/
example (x a : Nat) (l r : BT) (P : BT → Prop)
    (h : P (if a < x then prune x r else .bin (prune x l) a r)) : P (prune x (.bin l a r)) := by
  unfold prune
  exact h

/-! ### R4. `split` · goal list: `if c then u else v` in the goal → one goal per branch
The first goal gets `h✝ : c` and shows `u`; the second gets `h✝ : ¬c` and shows `v`. `h✝` is an
inaccessible name: `assumption` (R11) or `grind` (R6) still use it. -/
example {α : Type} (c : Prop) [Decidable c] (u v : α) (P : α → Prop) (hu : c → P u)
    (hv : ¬c → P v) : P (if c then u else v) := by
  split
  · exact hu ‹c›
  · exact hv ‹¬c›

/-! ### R5. `simp only [ih]` with `ih : A ↔ B` · goal: every `A` → `B`
An `↔` between propositions rewrites like an `=`; that is how an induction hypothesis of the form
`f … ↔ …` is used. Combine with R2: `simp only [f, ih]`. -/
example (A B : Prop) (P : Prop → Prop) (ih : A ↔ B) (h : P B) : P A := by
  simp only [ih]
  exact h

/-! ### R6. `grind` · closes goals of propositional logic (`∨ ∧ ¬ ↔`), equalities and linear
arithmetic over `Nat`, using the hypotheses. Here it needs `¬a < b`, `¬b < a` ⇒ `a = b`.
Any other subterm (`has y l`, `A`) is an opaque proposition to it. -/
example (y a b : Nat) (A B : Prop) (h1 : ¬a < b) (h2 : ¬b < a) :
    (A ∨ y = b ∨ B) ↔ (y = a ∨ B ∨ A ∨ y = b) := by
  grind

/-! ## Recursive `Prop` facts: take apart, build -/

/-! ### R7. `obtain ⟨ha, hl, hr⟩ := h` · context: `h : every p (bin l a r)` → its three parts
`every p (bin l a r)` unfolds to `p a ∧ every p l ∧ every p r`; `obtain` sees through the
definition by itself (no `simp` needed). -/
example (p : Nat → Prop) (a : Nat) (l r : BT) (G : Prop) (h : every p (.bin l a r))
    (g : p a → every p l → every p r → G) : G := by
  obtain ⟨ha, hl, hr⟩ := h
  exact g ha hl hr

/-! ### R8. `exact ⟨ha, hl, hr⟩` · closes `every p (bin l a r)` from proofs of the three parts
The anonymous constructor `⟨_, _, _⟩` also sees through the definition (it is `⟨_, ⟨_, _⟩⟩`). -/
example (p : Nat → Prop) (a : Nat) (l r : BT) (ha : p a) (hl : every p l) (hr : every p r) :
    every p (.bin l a r) := by
  exact ⟨ha, hl, hr⟩

/-! ## Inductive predicates -/

/-! ### R9. `induction h with | tip => ?_ | @bin l a r hl hr bl br ihl ihr => ?_` · goal list
Induction on a proof `h : Heap t`: one goal per constructor of `Heap`. `@` lets you name the
constructor's implicit arguments `{l a r}` too; then come its explicit arguments `hl hr bl br`, then
one induction hypothesis per recursive argument (`bl : Heap l` gives `ihl : Q l`). -/
example (Q : BT → Prop) (t : BT) (h : Heap t) (h0 : Q .tip)
    (h1 : ∀ l a r, every (· ≤ a) l → every (· ≤ a) r → Heap l → Heap r → Q l → Q r →
      Q (.bin l a r)) : Q t := by
  induction h with
    | tip => ?_
    | @bin l a r hl hr bl br ihl ihr => ?_
  exact h0
  exact h1 l a r hl hr bl br ihl ihr

/-! ### R10. `exact .bin h₁ h₂ h₃ h₄` · closes `Heap (bin l a r)` with a constructor
`.bin` is `Heap.bin` (the expected type names the inductive). `trivial` proves `every p .tip`,
which unfolds to `True`. -/
example (a : Nat) : Heap (.bin .tip a .tip) := by
  exact .bin trivial trivial .tip .tip

/-! `exact` compares up to computation: a function applied to a constructor (`mirror (bin tip a tip)`)
computes to a constructor, so the same term closes it with no unfolding step first. -/
example (a : Nat) : Heap (mirror (.bin .tip a .tip)) := by
  exact .bin trivial trivial .tip .tip

/-! ### R11. `(by assumption)` · closes a goal that is one of the hypotheses
It compares up to unfolding, so `h : x < k` proves `(fun y => y < k) x`. Inside a term, write
`(by assumption)` where a proof is expected; it also finds inaccessible `h✝`. -/
example (x k : Nat) (h : x < k) : (fun y => y < k) x := by
  assumption

/-! ### R12. `lem _ s hs` · term: `_` for an explicit argument Lean can infer
Here `p` is read off `hs : every (· < k) s`, so `lem _ s hs : every (· < k) (f s)`. -/
example (f : BT → BT) (k : Nat) (s : BT)
    (lem : ∀ (p : Nat → Prop) (s : BT), every p s → every p (f s)) (hs : every (· < k) s) :
    every (· < k) (f s) := by
  exact lem _ s hs

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An `↔` by induction: R1, then R2 with the induction hypotheses (R5), then R6 -/
example (y : Nat) (t : BT) : has y (mirror t) ↔ has y t := by
  induction t with
    | tip => simp [mirror, has]
    | bin l a r ihl ihr =>
      simp only [mirror, has, ihl, ihr]
      grind

/-! ### W2. A milestone: `prune` keeps `every p`. R1 (with `ht` carried), R7, R3, R4, R8 -/
theorem every_prune (p : Nat → Prop) (x : Nat) (t : BT) (ht : every p t) :
    every p (prune x t) := by
  induction t with
    | tip => simp [prune, every]
    | bin l a r ihl ihr =>
      obtain ⟨ha, hl, hr⟩ := ht
      unfold prune
      split
      · exact ihr hr
      · exact ⟨ha, ihl hl, hr⟩

/-! ### W3. Using the milestone: `prune` keeps `Heap`. R9, R3, R4, R10 with R12 -/
example (x : Nat) (t : BT) (h : Heap t) : Heap (prune x t) := by
  induction h with
    | tip => exact .tip
    | @bin l a r hl hr bl br ihl ihr =>
      unfold prune
      split
      · exact ihr
      · exact .bin (every_prune _ x l hl) hr ihl br

end M019Guide

/- Guide for M021 (Partition is a permutation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own object, which is NOT the exercise's:
  `tally q l`   a pair of counters `(number of x with q x, number of x without)`, computed in one
                pass with a `let` and an `if`, like the exercise's `partition`.
Part W: worked combinations on `tally` and on plain lists.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M021Guide

/-- `tally q l`: how many elements of `l` satisfy `q`, and how many do not. -/
def tally (q : Nat → Bool) : List Nat → Nat × Nat
  | [] => (0, 0)
  | x :: xs =>
    let r := tally q xs
    if q x then (r.1 + 1, r.2) else (r.1, r.2 + 1)

/-! # Part R · Reference entries -/

/-! ## Induction on a list and closing the base case -/

/-! ### R1. `induction l with | nil => … | cons x xs ih => …` · goal list: `[]` and `x :: xs`
`ih` is the statement for the tail `xs`. The arms here are `?_`, so both goals stay open. -/
example (P : List Nat → Prop) (h0 : P []) (h1 : ∀ x xs, P xs → P (x :: xs)) (l : List Nat) :
    P l := by
  induction l with | nil => ?_ | cons x xs ih => ?_
  · exact h0
  · exact h1 x xs ih

/-! ### R2. `rfl` · closes `a = b` when both sides compute to the same value
`tally q []` and `List.filter q []` evaluate by their `[]` clauses. -/
example (q : Nat → Bool) : (tally q [], List.filter q []) = ((0, 0), []) := by
  rfl

/-! ## Splitting on a Boolean -/

/-! ### R3. `cases h : q x` · goal list: one goal per value of `q x`; context gains `h`
`false` comes first (it is `Bool`'s first constructor). Every visible `q x` in the goal is replaced
by the value. When `q x` is hidden inside a definition, the goal looks unchanged; only `h` is new. -/
example (q : Nat → Bool) (x : Nat) (P : Bool → Prop) (hf : P false) (ht : P true) : P (q x) := by
  cases h : q x
  · exact hf
  · exact ht

/-! ## Evaluating one step of a `def` with `let` and `if` -/

/-! ### R4. `simp only [f]` · goal: unfold the `::` clause of `f`, substituting the `let`
`let r := tally q xs` disappears: `r` is replaced by its value. `r.1`, `r.2` print as `.fst`, `.snd`.
A call on a variable list (`tally q xs`) stays as it is. -/
example (q : Nat → Bool) (x : Nat) (xs : List Nat) (P : Nat × Nat → Prop)
    (h : P (if q x = true then ((tally q xs).fst + 1, (tally q xs).snd)
            else ((tally q xs).fst, (tally q xs).snd + 1))) :
    P (tally q (x :: xs)) := by
  simp only [tally]
  exact h

/-! ### R5. `List.filter_cons` · `filter q (x :: xs) = if q x = true then x :: filter q xs else filter q xs`
`List.filter q l` keeps the elements `y` of `l` with `q y = true`. The `if` tests `q x = true`: a
`Bool` used as a condition is turned into the proposition `q x = true`. -/
example {α : Type} (q : α → Bool) (x : α) (xs : List α) (P : List α → Prop)
    (h : P (if q x = true then x :: List.filter q xs else List.filter q xs)) :
    P (List.filter q (x :: xs)) := by
  rw [List.filter_cons]
  exact h

/-! ### R6. `simp only [h]` (`h : b = true` or `h : b = false`) · goal: `b` → its value
With `h : q x = true`, the condition `q x = true` becomes `true = true`, which `simp` turns into
`True` at once. With `h : q x = false` it becomes `false = true` and stays (R7). -/
example {α : Type} (q : Nat → Bool) (x : Nat) (a e : α) (P : α → Prop) (hq : q x = false)
    (h : P (if false = true then a else e)) : P (if q x = true then a else e) := by
  simp only [hq]
  exact h

/-! ### R7. `Bool.false_eq_true` · `(false = true) = False` · goal: the false condition → `False` -/
example {α : Type} (a e : α) (P : α → Prop) (h : P (if False then a else e)) :
    P (if false = true then a else e) := by
  simp only [Bool.false_eq_true]
  exact h

/-! ### R8. `if_true`, `if_false` · `(if True then a else e) = a`, `(if False then a else e) = e` -/
example {α : Type} (a e : α) (P : α → Prop) (h : P a ∧ P e) :
    P (if True then a else e) ∧ P (if False then a else e) := by
  simp only [if_true, if_false]
  exact h

/-! ### R9. `Bool.not_true`, `Bool.not_false` · `(!true) = false`, `(!false) = true`
`!b` is Boolean negation (`Bool.not b`). In the exercise it comes from the predicate `fun x => !p x`. -/
example (P : Bool → Bool → Prop) (h : P false true) : P (!true) (!false) := by
  simp only [Bool.not_true, Bool.not_false]
  exact h

/-! ### R10. pair projections `(a, b).fst = a`, `(a, b).snd = b` · goal: `simp` reduces them itself
Every `simp only […]` call does this, even with an empty list. -/
example {α β : Type} (a : α) (b : β) (P : α → β → Prop) (h : P a b) :
    P (a, b).fst (a, b).snd := by
  simp only []
  exact h

/-! ## Using a proved theorem and permutations -/

/-! ### R11. `rw [lem]` (`lem : ∀ l, f l = g l`) · goal: every `f l` → `g l`
`rw` instantiates `lem` with the first match, then rewrites all copies of that instance. -/
example (f g : List Nat → Nat × Nat) (lem : ∀ l, f l = g l) (l : List Nat)
    (P : Nat × Nat → Nat × Nat → Prop) (h : P (g l) (g l)) : P (f l) (f l) := by
  rw [lem]
  exact h

/-! ### R12. `exact .refl _` (lemma `List.Perm.refl`) · closes `l.Perm l`, also up to computation
`List.Perm.refl l : l.Perm l`. `exact` accepts the goal below because `List.filter q []` and
`[] ++ []` both compute to `[]`. -/
example (q r : Nat → Bool) : (List.filter q [] ++ List.filter r []).Perm [] := by
  exact .refl _

/-! ### R13. `simp only [l₁, h] at ih ⊢` · context and goal: the same rewriting in `ih` and the goal
`at ih` rewrites only `ih`; `⊢` stands for the goal. It fails only if it changes neither. -/
example {α : Type} (q : α → Bool) (x : α) (xs : List α) (hq : q x = true)
    (P Q : List α → Prop) (ih : P (List.filter q (x :: xs)))
    (h : P (x :: List.filter q xs) → Q (x :: List.filter q xs)) :
    Q (List.filter q (x :: xs)) := by
  simp only [List.filter_cons, hq, if_true] at ih ⊢
  exact h ih

/-! ### R14. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal: pull the head out of `++`
`a :: as ++ bs` parses as `(a :: as) ++ bs`. -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (h : P (a :: (as ++ bs))) :
    P (a :: as ++ bs) := by
  rw [List.cons_append]
  exact h

/-! ### R15. `List.perm_middle` · `(l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))` · closes the goal
`l₁.Perm l₂` (`List.Perm`) says `l₂` is a rearrangement of `l₁`. This lemma moves an element from
the middle to the front. All its arguments `{a l₁ l₂}` are implicit: Lean reads them off the goal. -/
example {α : Type} (a : α) (l₁ l₂ : List α) : (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂)) := by
  exact List.perm_middle

/-! ### R16. `List.Perm.trans` · `l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃` · goal: one step of a chain
As a term: `h.trans h'`. `refine h.trans ?_` uses `h` for the first step; the goal is the rest. -/
example {α : Type} (l₁ l₂ l₃ : List α) (h : l₁.Perm l₂) (h' : l₂.Perm l₃) : l₁.Perm l₃ := by
  refine h.trans ?_
  exact h'

/-! ### R17. `List.Perm.cons` · `l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)` · goal: drop the common head
As a term: `h.cons a`, for `h : l₁.Perm l₂`. -/
example {α : Type} (a : α) (l₁ l₂ : List α) (h : l₁.Perm l₂) : (a :: l₁).Perm (a :: l₂) := by
  apply List.Perm.cons
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Induction, `cases h : q x`, one `simp` with the def and `h`, then `omega` uses `ih`: R1–R4, R6–R10 -/
example (q : Nat → Bool) (l : List Nat) : (tally q l).1 + (tally q l).2 = l.length := by
  induction l with
    | nil => rfl
    | cons x xs ih =>
      cases h : q x <;> simp [tally, h] <;> omega

/-! ### W2. Two middle elements to the front: R15 twice, glued by R16 and R17 -/
example {α : Type} (a b : α) (l₁ l₂ : List α) :
    (l₁ ++ a :: b :: l₂).Perm (a :: b :: (l₁ ++ l₂)) := by
  refine List.perm_middle.trans ?_
  exact List.perm_middle.cons a

/-! ### W3. A chain with an IH, as in a list induction: R16, R15, R17 -/
example {α : Type} (a : α) (l₁ l₂ l : List α) (ih : (l₁ ++ l₂).Perm l) :
    (l₁ ++ a :: l₂).Perm (a :: l) := by
  exact List.perm_middle.trans (ih.cons a)

end M021Guide

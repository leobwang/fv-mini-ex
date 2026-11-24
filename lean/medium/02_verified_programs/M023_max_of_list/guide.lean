/- Guide for M023 (Max of a non-empty list).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own functions, which are NOT the exercise's:
  `lastOf x xs`  the last element of the non-empty list `x :: xs`; the first argument carries the
                 element seen most recently (R1);
  `lenAcc n xs`  `n` plus the length of `xs`; the first argument is a counter (R1).
Part W: worked combinations on `lenAcc` and `lastOf`.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M023Guide

/-! # Part R · Reference entries -/

/-! ## Writing the function -/

/-! ### R1. `match xs with | [] => x | y :: ys => f (new x) ys` · term: recursion with an accumulator
The list argument shrinks (`ys` is the tail of `xs`), so Lean accepts the recursion; the OTHER
argument changes from call to call (`y` here, `n + 1` below). Each arm is one equation that
`simp [f]` / `simp only [f]` can use (R6, R7). -/
def lastOf {α : Type} (x : α) (xs : List α) : α :=
  match xs with
  | [] => x
  | y :: ys => lastOf y ys

def lenAcc {α : Type} (n : Nat) (xs : List α) : Nat :=
  match xs with
  | [] => n
  | _ :: ys => lenAcc (n + 1) ys

example : lastOf 1 [2, 3] = 3 ∧ lenAcc 10 [1, 2, 3] = 13 := ⟨rfl, rfl⟩

/-! ### R2. `max a b` · term: the larger of `a` and `b`
`max a b` on `Int` is `if a ≤ b then b else a`. `omega` knows `max` (R12). -/
example : max (3 : Int) (-5) = 3 ∧ max (-1 : Int) 4 = 4 := by decide

/-! ## Induction with a re-quantified accumulator -/

/-! ### R3. `induction xs generalizing x with | nil => ?_ | cons z zs ih => ?_` · goal list: `[]` and
`z :: zs`; context: `ih : ∀ (x : α), …`
`generalizing x` takes `x` out of the context first, so `ih` holds for EVERY first argument: you
will use it at the new accumulator (`max x z` in the exercise), not at `x`. -/
example {α : Type} (P : α → List α → Prop) (h0 : ∀ x, P x [])
    (hs : ∀ z zs, (∀ x, P x zs) → ∀ x, P x (z :: zs)) (x : α) (xs : List α) : P x xs := by
  induction xs generalizing x with | nil => ?_ | cons z zs ih => ?_
  · exact h0 x
  · exact hs z zs ih x

/-! ### R4. `intro y hy` · goal `∀ y ∈ l, Q y` → context gains `y` and `hy : y ∈ l`
`∀ y ∈ l, Q y` is notation for `∀ y, y ∈ l → Q y`: two binders, so two names. -/
example {α : Type} (l : List α) (Q : α → Prop) (hq : ∀ y, y ∈ l → Q y) : ∀ y ∈ l, Q y := by
  intro y hy
  exact hq y hy

/-! ## The `nil` case -/

/-! ### R5. `simp at hy` (lemma `List.mem_singleton`) · context: `hy : y ∈ [a]` → `hy : y = a` -/
example {α : Type} (a y : α) (G : Prop) (hg : y = a → G) (hy : y ∈ [a]) : G := by
  simp at hy
  exact hg hy

/-! ### R6. `simp [f, hy]` · closes the goal: unfold `f` at `[]`, rewrite with `hy`, then `a ≤ a`
(or `a ∈ [a]`) is `True`. -/
example (n m : Nat) (hy : m = n) : m ≤ lenAcc n ([] : List Nat) := by
  simp [lenAcc, hy]

example {α : Type} (a : α) : lastOf a [] ∈ [a] := by
  simp [lastOf]

/-! ## The `cons` case -/

/-! ### R7. `simp only [f]` · goal: `f x (z :: zs)` → the right side of `f`'s `::` equation
It unfolds only where the list argument is literally `[]` or `_ :: _`. -/
example {α : Type} (x z : α) (zs : List α) (P : α → Prop) (h : P (lastOf z zs)) :
    P (lastOf x (z :: zs)) := by
  simp only [lastOf]
  exact h

/-! ### R8. `have h := ih e` · context gains `ih` at the argument `e`
After R3, `ih : ∀ (x : α), Q x` is a function; `ih e : Q e`. Give more arguments for more `∀`s and
`→`s: `ih e y hy`. -/
example {α : Type} (Q : α → Prop) (e : α) (G : Prop) (hg : Q e → G) (ih : ∀ x, Q x) : G := by
  have h := ih e
  exact hg h

/-! ### R9. `List.mem_cons_self` · term: `a ∈ a :: l` (the head is a member)
Its arguments `a`, `l` are implicit: Lean reads them off the expected type. -/
example {α : Type} (a : α) (l : List α) : a ∈ a :: l := List.mem_cons_self

/-! ### R10. `simp only [List.mem_cons] at h ⊢` · context and goal: `a ∈ b :: l` → `a = b ∨ a ∈ l`
`at h ⊢` rewrites the hypothesis `h` and the goal; `at hy` only `hy`. On `a ∈ b :: c :: l` it
fires twice: `a = b ∨ a = c ∨ a ∈ l`. -/
example {α : Type} (a b c : α) (l : List α) (G : Prop) (hg : a = b ∨ a = c ∨ a ∈ l → G)
    (hy : a ∈ b :: c :: l) : G := by
  simp only [List.mem_cons] at hy
  exact hg hy

-- R10, second form: `at h ⊢` rewrites the hypothesis `h` AND the goal in one step.
example {α : Type} (a b c : α) (l : List α) (hg : a = b ∨ a ∈ l → a = c ∨ a = b ∨ a ∈ l)
    (h : a ∈ b :: l) : a ∈ c :: b :: l := by
  simp only [List.mem_cons] at h ⊢
  exact hg h

/-! ### R11. `rcases hy with rfl | rfl | hy` · goal list: one goal per disjunct
`|` splits `∨` (nested to the right). The pattern `rfl` on `y = a` substitutes: when `a` is a
variable it is replaced by `y` everywhere (otherwise `y` is replaced by `a`), and the equation
disappears. -/
example {α : Type} (y a b : α) (l : List α) (P : α → Prop) (ha : P a) (hb : P b)
    (hl : ∀ x, x ∈ l → P x) (hy : y = a ∨ y = b ∨ y ∈ l) : P y := by
  rcases hy with rfl | rfl | hy
  · exact ha
  · exact hb
  · exact hl y hy

/-! ### R12. `omega` · closes linear arithmetic over `Int`/`Nat`, including `max` and `min`
Any other term, such as `f (max a b) l`, counts as one unknown number. -/
example (a b : Int) (f : Int → List Int → Int) (l : List Int) (hmax : max a b ≤ f (max a b) l) :
    a ≤ f (max a b) l := by
  omega

/-! ### R13. `List.mem_cons_of_mem` · term: `a ∈ l → a ∈ b :: l`; the head `b` is explicit -/
example {α : Type} (a b : α) (l : List α) (h : a ∈ l) : a ∈ b :: l := List.mem_cons_of_mem b h

/-! ### R14. `grind` · closes the goal by combining hypotheses, equalities, `∨` and arithmetic
Here it needs `max a b = a ∨ max a b = b`, which it derives itself; `omega` cannot do this, since
the goal also mentions `m ∈ l`, which is not arithmetic. -/
example (a b m : Int) (l : List Int) (h : m = max a b ∨ m ∈ l) : m = a ∨ m = b ∨ m ∈ l := by
  grind

/-! # Part W · Worked combinations (on `lenAcc` and `lastOf`, not the exercise's function) -/

/-- W1. An accumulator lower bound: R3, R6 for `nil`; R7, R8 at the new counter, R12 for `cons`. -/
theorem le_lenAcc {α : Type} (n : Nat) (xs : List α) : n ≤ lenAcc n xs := by
  induction xs generalizing n with | nil => ?_ | cons z zs ih => ?_
  · simp [lenAcc]
  simp only [lenAcc]
  have h := ih (n + 1)
  omega

/-- W2. The result is a member: R3, R6 for `nil`; R7, R8 at the new accumulator, R10, R14. -/
theorem lastOf_mem {α : Type} (x : α) (xs : List α) : lastOf x xs ∈ x :: xs := by
  induction xs generalizing x with | nil => ?_ | cons z zs ih => ?_
  · simp [lastOf]
  simp only [lastOf]
  have h := ih z
  simp only [List.mem_cons] at h ⊢
  grind

end M023Guide

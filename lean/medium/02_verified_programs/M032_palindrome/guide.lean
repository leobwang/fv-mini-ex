/- Guide for M032 (Palindrome).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own object, which is NOT the exercise's:
  `isNil l`   a `Bool` test `l == []` (R2), used to show unfolding (R3) and `==` → `=` (R4).
Part W: worked combinations on `isNil` and on two lists of equal length.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M032Guide

/-! # Part R · Reference entries -/

/-! ## Writing the function -/

/-! ### R1. `l.reverse` (`List.reverse`) · term: the list in the opposite order
`l.reverse` is the same as `List.reverse l`. -/
example : [1, 2, 3].reverse = [3, 2, 1] := rfl

/-! ### R2. `a == b` · term: a `Bool` comparison (type class `BEq`)
`==` returns a `Bool`, not a `Prop`. On `List Nat` it compares the lists entry by entry. A
theorem about a `Bool` function `f` is stated as `f x = true`. -/
example : ([1, 2] == [1, 2]) = true ∧ ([1, 2] == [2, 1]) = false := ⟨rfl, rfl⟩

/-- `isNil l`: is `l` the empty list? A `Bool` test written with `==` (R2). -/
def isNil (l : List Nat) : Bool := l == []

/-! ## From `Bool` to `Prop` -/

/-! ### R3. `simp only [f]` · goal: the name `f` applied to an argument → its body -/
example (l : List Nat) (P : Prop → Prop) (h : P ((l == []) = true)) : P (isNil l = true) := by
  simp only [isNil]
  exact h

/-! ### R4. `beq_iff_eq` · `(a == b) = true ↔ a = b` · goal: a `Bool` test → an equation
Needs `[BEq α] [LawfulBEq α]`: `==` exists on `α` and agrees with `=`. `Nat`, `Bool`, `List Nat`
qualify. -/
example {α : Type} [BEq α] [LawfulBEq α] (a b : α) (P : Prop → Prop) (h : P (a = b)) :
    P ((a == b) = true) := by
  simp only [beq_iff_eq]
  exact h

/-! ## Two directions, bounded quantifiers -/

/-! ### R5. `constructor` on `A ↔ B` · goal list: `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  · exact hab
  · exact hba

/-! ### R6. `intro h i hi` on `A → ∀ i < n, Q i` · context gains `h`, `i`, `hi`; goal `Q i`
`∀ i < n, Q i` is notation for `∀ i, i < n → Q i`; the infoview prints the long form. -/
example (A : Prop) (n : Nat) (Q : Nat → Prop) (hq : ∀ i, i < n → Q i) :
    A → ∀ i < n, Q i := by
  intro h i hi
  exact hq i hi

/-! ## Rewriting one side only -/

/-! ### R7. `conv => lhs; rw [h]` · goal: rewrite inside the left-hand side only
`conv` enters a part of the goal; `lhs` selects the left side of `x = y` (more generally the
second-to-last argument, so also `x` in `R x y`); `rw [h]` acts there only. Compare plain
`rw [h]` below, which rewrites every copy of `a`. -/
example (R : Nat → Nat → Prop) (a b : Nat) (h : a = b) (hp : R b a) : R a a := by
  conv => lhs; rw [h]
  exact hp

example (R : Nat → Nat → Prop) (a b : Nat) (h : a = b) (hp : R b b) : R a a := by
  rw [h]
  exact hp

/-! ## Indexing a list -/

/-! ### R8. `List.getElem?_reverse` · `i < l.length → l.reverse[i]? = l[l.length - 1 - i]?` · goal
`l[i]?` is entry `i` of `l` (counting from 0) as an `Option`: `some` of the entry if
`i < l.length`, `none` otherwise. Pass the bound: `List.getElem?_reverse hi`. -/
example {α : Type} (l : List α) (i : Nat) (hi : i < l.length) (P : Option α → Prop)
    (h : P l[l.length - 1 - i]?) : P l.reverse[i]? := by
  rw [List.getElem?_reverse hi]
  exact h

/-! ### R9. `apply List.ext_getElem?` · goal `l₁ = l₂` → `∀ i, l₁[i]? = l₂[i]?`
Lemma: `(∀ i, l₁[i]? = l₂[i]?) → l₁ = l₂`. Two lists are equal when every index agrees,
in range (`some`) and out of range (`none`) alike. -/
example {α : Type} (l₁ l₂ : List α) (h : ∀ i : Nat, l₁[i]? = l₂[i]?) : l₁ = l₂ := by
  apply List.ext_getElem?
  exact h

/-! ### R10. `by_cases hi : i < n` · goal list: one goal with `hi : i < n`, one with `hi : ¬i < n` -/
example (n i : Nat) (G : Prop) (h1 : i < n → G) (h2 : ¬i < n → G) : G := by
  by_cases hi : i < n
  · exact h1 hi
  · exact h2 hi

/-! ### R11. `rw [h i hi]` with `h : ∀ i, i < n → l[i]? = m[i]?` · goal
`h i hi` is `h` applied to the index `i` and the bound `hi`: the equation `l[i]? = m[i]?`. -/
example {α : Type} (l m : List α) (n i : Nat) (h : ∀ i, i < n → l[i]? = m[i]?) (hi : i < n)
    (P : Option α → Prop) (hp : P m[i]?) : P l[i]? := by
  rw [h i hi]
  exact hp

/-! ### R12. `omega` · closes linear arithmetic on `Nat`/`Int`, using the hypotheses
It reads `¬i < n` as `n ≤ i`, and treats `l.length` as an unknown number. -/
example (n i : Nat) (hi : ¬i < n) : n ≤ i := by omega

/-! ### R13. `List.getElem?_eq_none` · `l.length ≤ i → l[i]? = none` · goal
Write `rw [List.getElem?_eq_none (by omega)]`: `rw` first finds `l[i]?` in the goal (the
first one, left to right), then `by omega` proves `l.length ≤ i` for that `l` and `i`. -/
example {α : Type} (l : List α) (i : Nat) (hi : ¬i < l.length) (P : Option α → Prop)
    (h : P none) : P l[i]? := by
  rw [List.getElem?_eq_none (by omega)]
  exact h

/-! ### R14. `List.length_reverse` · `l.reverse.length = l.length` · goal
`simp` applies it by itself: `(by simp; omega)` proves `l.reverse.length ≤ i` from `¬i < l.length`. -/
example {α : Type} (l : List α) (P : Nat → Prop) (h : P l.length) : P l.reverse.length := by
  rw [List.length_reverse]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Unfold a `Bool` test and turn `==` into `=` in one `simp only`: R3, R4 -/
example (l : List Nat) (P : Prop → Prop) (h : P (l = [])) : P (isNil l = true) := by
  simp only [isNil, beq_iff_eq]
  exact h

/-! ### W2. Two lists of equal length that agree below the length are equal: R9, R10, R11, R13
Out of range both sides are `none`; the second bound needs `hlen`, which `omega` uses. -/
example (l m : List Nat) (hlen : l.length = m.length) (h : ∀ i, i < l.length → l[i]? = m[i]?) :
    l = m := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < l.length
  · rw [h i hi]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ### W3. A bound on a reversed list: R13 with R14 inside the side proof -/
example (l : List Nat) (i : Nat) (hi : ¬i < l.length) : l.reverse[i]? = none := by
  rw [List.getElem?_eq_none (by simp; omega)]

end M032Guide

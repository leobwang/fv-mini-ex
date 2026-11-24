/- Guide for E086 (Strings and chars).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: a worked combination on an object that is NOT the exercise's (lengths instead of counts).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is in core Lean.
-/

namespace E086Guide

/-! # Part R · Reference entries -/

/-! ## Literals: evaluate, do not prove -/

/-! ### R1. `decide` on `String` / `Char` literals · closes the goal
`"ab"` is a `String`, `'b'` a `Char`; `.length`, `.toNat` (code point), `.isDigit` (a `Bool`) all
compute on literals, so `decide` evaluates both sides and closes the goal. -/
example : "ab".length = 2 ∧ 'b'.toNat = 98 ∧ 'x'.isDigit = false := by
  decide

/-! ### R2. `String.toList` · `s.toList : List Char`; on a literal, `decide` closes the goal
A `String` is UTF-8 bytes, not a list. `.toList` gives its characters as a `List Char`, where all
of the `List` library applies. `++` on strings is concatenation. -/
example : ("h" ++ "i").toList = ['h', 'i'] := by
  decide

/-! ### R3. `List.countP p l` · counts the entries `x` of `l` with `p x = true` (`p : α → Bool`)
On a literal list `decide` closes the goal. A `Char` test such as `Char.isUpper` is a valid `p`,
and the list can come from R2. -/
example : "aBcD".toList.countP Char.isUpper = 2 := by
  decide

/-! ## Unfolding your own definition -/

/-! ### R4. `unfold f` · goal: the name `f` applied to arguments → its body -/
def twice (s : String) : String := s ++ s
example (s : String) (P : String → Prop) (h : P (s ++ s)) : P (twice s) := by
  unfold twice
  exact h

/-! ## One character: `String.singleton` -/

/-! ### R5. `String.toList_singleton` · `(String.singleton c).toList = [c]` · goal -/
example (c : Char) (P : List Char → Prop) (h : P [c]) : P (String.singleton c).toList := by
  rw [String.toList_singleton]
  exact h

/-! ### R6. `List.countP_singleton` · `countP p [a] = if p a = true then 1 else 0` · goal -/
example {α : Type} (p : α → Bool) (a : α) (P : Nat → Prop)
    (h : P (if p a = true then 1 else 0)) : P ([a].countP p) := by
  rw [List.countP_singleton]
  exact h

/-! ## Concatenation: `++` -/

/-! ### R7. `String.toList_append` · `(s ++ t).toList = s.toList ++ t.toList` · goal -/
example (s t : String) (P : List Char → Prop) (h : P (s.toList ++ t.toList)) :
    P (s ++ t).toList := by
  rw [String.toList_append]
  exact h

/-! ### R8. `List.countP_append` · `countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂` · goal -/
example {α : Type} (p : α → Bool) (l₁ l₂ : List α) (P : Nat → Prop)
    (h : P (l₁.countP p + l₂.countP p)) : P ((l₁ ++ l₂).countP p) := by
  rw [List.countP_append]
  exact h

/-! ## Length -/

/-! ### R9. `String.length_toList` · `s.toList.length = s.length`; right to left: `rw [← …]` · goal
`simp` does not use this lemma: on `… ≤ s.length` it makes no progress. -/
example (s : String) (P : Nat → Prop) (h : P s.toList.length) : P s.length := by
  rw [← String.length_toList]
  exact h

/-! ### R10. `List.countP_le_length` · `countP p l ≤ l.length` · closes the goal -/
example {α : Type} (p : α → Bool) (l : List α) : l.countP p ≤ l.length := by
  exact List.countP_le_length

/-! # Part W · Worked combination (not the exercise's object) -/

/-! ### W1. String → list (R7), then a list lemma: `List.length_append`
`List.length_append : (l₁ ++ l₂).length = l₁.length + l₂.length`. -/
example (s t : String) : (s ++ t).toList.length = s.toList.length + t.toList.length := by
  rw [String.toList_append]
  rw [List.length_append]

end E086Guide

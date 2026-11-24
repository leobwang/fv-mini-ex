/- Guide for E030 (Prop-valued definitions).
Part R: one reference entry per tactic, term or lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G` is an
arbitrary goal (a `Prop`) when the step does not look at the goal. A hypothesis `k` in an entry is
only there to finish the example; it shows what the goal or the context became.
All entries use the guide's own predicates `SomeP`, `Image` and `AllIn` below, NOT the exercise's.
Part W: worked combinations on other predicates (`Even2`, `Bounded`).
Assumed: Lean basics up to E029, in particular `intro`/`exact` (E003), anonymous constructors
`⟨_, _⟩` (E004), `rcases` on `∨` (E006), `∃` and `obtain` (E007), `rw` (E009), `unfold` (E012),
`show` (E021) and bounded quantifiers `∀ x ∈ xs, …` (E025).
-/

namespace E030Guide

/-- An `∃` behind a name: some value satisfies `p`. -/
def SomeP {α : Type} (p : α → Prop) : Prop := ∃ x, p x

/-- An `∃` whose body is an equation `y = f x`: `y` is in the image of `f`. -/
def Image {α β : Type} (f : α → β) (y : β) : Prop := ∃ x, y = f x

/-- A bounded `∀` behind a name: every element of `xs` satisfies `p`. -/
def AllIn {α : Type} (p : α → Prop) (xs : List α) : Prop := ∀ x ∈ xs, p x

/-! # Part R · Reference entries -/

/-! ## Seeing the body of a definition -/

/-! ### R1. `unfold D` · goal: the name `D …` → its body
A `def … : Prop` is a function into `Prop`: `SomeP p` is a proposition whose meaning is its body
`∃ x, p x`. `unfold SomeP` replaces the name by that body, so you see what to prove. -/
example {α : Type} (p : α → Prop) (h : ∃ x, p x) : SomeP p := by
  unfold SomeP
  exact h

/-! ### R2. `show T` · goal → `T`, any statement definitionally equal to it
`show` accepts `T` when Lean can unfold both sides to the same term. Use it to write the body
out yourself (or a simplified form of it). -/
example {α : Type} (p : α → Prop) (h : ∃ x, p x) : SomeP p := by
  show ∃ x, p x
  exact h

/-! ## Proving a defined `∃` -/

/-! ### R3. `exact ⟨w, hw⟩` · closes `D …` when `D`'s body is `∃ x, …`
The anonymous constructor (E004, E007) sees through definitions on its own: no `unfold` needed.
The same term works after `:=` in term mode. -/
example {α : Type} (p : α → Prop) (w : α) (hw : p w) : SomeP p := by
  exact ⟨w, hw⟩

/-! ### R4. `Nat.mul_one` · `n * 1 = n` · goal: `a * 1` → `a` -/
example (a : Nat) (P : Nat → Prop) (h : P a) : P (a * 1) := by
  rw [Nat.mul_one]
  exact h

/-! ### R5. `h.symm` (`Eq.symm`) · from `h : a = b` get `b = a`
`Nat.mul_one a : a * 1 = a`, so `(Nat.mul_one a).symm : a = a * 1`. Write `(lemma args).symm`
with the parentheses. -/
example {α : Type} (a b : α) (h : a = b) : b = a := by
  exact h.symm

/-! ## Using a defined `∃` -/

/-! ### R6. `obtain ⟨x, hx⟩ := h` · context: `h : D …` (body `∃ x, q x`) → `x`, `hx : q x`
Like the anonymous constructor, `obtain` sees through the definition. -/
example {α : Type} (p : α → Prop) (G : Prop) (k : ∀ x, p x → G) (h : SomeP p) : G := by
  obtain ⟨x, hx⟩ := h
  exact k x hx

/-! ### R7. `obtain ⟨x, rfl⟩ := h` · context loses `y`; `y` is replaced by `f x` everywhere
When the body is an equation `y = f x` and `y` is a local variable, the pattern `rfl` substitutes
it: `y` disappears from the context, and every hypothesis and the goal that mentioned `y` now
mention `f x`. -/
example {α β : Type} (f : α → β) (y : β) (P : β → Prop) (k : ∀ x, P (f x)) (h : Image f y) :
    P y := by
  obtain ⟨x, rfl⟩ := h
  exact k x

/-! ### R8. `Nat.mul_assoc` · `a * b * c = a * (b * c)` · goal: regroup a product
`*` groups to the left, so `a * b * c` is `(a * b) * c`. As a term, `Nat.mul_assoc a b c` is the
equation itself. -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * (b * c))) : P (a * b * c) := by
  rw [Nat.mul_assoc]
  exact h

/-! ## Proving a defined bounded `∀` -/

/-! ### R9. `unfold D at *` · goal AND context: every `D …` → its body
`at h` unfolds in the hypothesis `h` only; `at *` unfolds in every hypothesis and in the goal. -/
example {α : Type} (p : α → Prop) (xs ys : List α) (k : (∀ x ∈ xs, p x) → ∀ x ∈ ys, p x)
    (h : AllIn p xs) : AllIn p ys := by
  unfold AllIn at *
  exact k h

/-! ### R10. `intro y hy` · goal `∀ x ∈ xs, Q x` → `Q y`; context gains `y`, `hy : y ∈ xs`
`∀ x ∈ xs, Q x` is `∀ x, x ∈ xs → Q x` (E025): two binders, so `intro` takes two names. -/
example {α : Type} (p : α → Prop) (xs : List α) (k : ∀ y, y ∈ xs → p y) : ∀ x ∈ xs, p x := by
  intro y hy
  exact k y hy

/-! ### R11. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l` · context: membership in a cons → `∨`
`rw` with an `↔` rewrites a proposition. `rw [List.mem_cons] at hy` changes the hypothesis `hy`. -/
example {α : Type} (a b : α) (l : List α) (G : Prop) (k : a = b ∨ a ∈ l → G) (hy : a ∈ b :: l) :
    G := by
  rw [List.mem_cons] at hy
  exact k hy

/-! ### R12. `rcases hy with rfl | hy` · goal list: one goal per side of `∨`
Left side `a = b`: the pattern `rfl` substitutes. With a local variable on both sides, Lean removes
the RIGHT one: `b` disappears and every `b` becomes `a` (so `hb : P b` becomes `hb : P a`). Names of
hypotheses stay. Right side: `hy : a ∈ l`, kept under the name given after `|`. -/
example {α : Type} (a b : α) (l : List α) (P : α → Prop) (hb : P b) (hl : ∀ z ∈ l, P z)
    (hy : a = b ∨ a ∈ l) : P a := by
  rcases hy with rfl | hy
  · exact hb
  · exact hl a hy

/-! ### R13. `h y hy` · use a bounded `∀`: `h : ∀ x ∈ xs, Q x`, `hy : y ∈ xs` give `Q y`
A bounded `∀` is a function of two arguments: the element, then the proof that it is in the list. -/
example {α : Type} (p : α → Prop) (xs : List α) (y : α) (h : ∀ x ∈ xs, p x) (hy : y ∈ xs) :
    p y := by
  exact h y hy

/-! # Part W · Worked combinations (on other predicates, not the exercise's) -/

/-- An even number: twice something. -/
def Even2 (n : Nat) : Prop := ∃ k, n = k + k

/-- Every element of the list is at least `a`. -/
def Bounded (a : Nat) (xs : List Nat) : Prop := ∀ x ∈ xs, a ≤ x

/-! ### W1. A defined `∃`, proved with a witness: R3 (with an equation proved by `rfl`) -/
example : Even2 6 := by
  exact ⟨3, rfl⟩

/-! ### W2. Unpack with `rfl` (R7), then give a new witness (R3) -/
example (n : Nat) (h : Even2 n) : Even2 (n + 2) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + 1, by omega⟩

/-! ### W3. A defined bounded `∀` over an append: R9, R10, then the R11 pattern with two other
membership lemmas, `List.mem_append : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` and
`List.mem_singleton : a ∈ [b] ↔ a = b`, then R12 (without `rfl`) and R13 -/
example (a x : Nat) (xs : List Nat) (hx : a ≤ x) (h : Bounded a xs) : Bounded a (xs ++ [x]) := by
  unfold Bounded at *
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact h y hy
  · rw [List.mem_singleton] at hy
    rw [hy]
    exact hx

/-! ### W4. `omega` sees neither a defined name nor an `∃`: unfold (R9), unpack (R6), then `omega` -/
example (n : Nat) (h : Even2 n) (h1 : n = 3) : False := by
  unfold Even2 at h
  obtain ⟨k, hk⟩ := h
  omega

end E030Guide

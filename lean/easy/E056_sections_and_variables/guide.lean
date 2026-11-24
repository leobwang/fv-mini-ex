/- Guide for E056 (Sections and variables).
Part R: one reference entry per command, tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The section entries (R1, R2, R4, R6, R7) are named `theorem`s on purpose: an `example` inside a
section sees EVERY `variable`, a `theorem` only the ones its statement mentions (or `include`s).
Part W: worked combinations on objects that are NOT the exercise's (`snoc`, `thrice`, `Rect.perim`).
Assumed: Lean basics (E001–E033).
-/

namespace E056Guide

/-! # Part R · Reference entries -/

/-! ## Section variables -/

section RefSec
-- Every declaration up to `end RefSec` may use these names without binding them itself.
variable {α : Type} (l m : List α) (x : α) (hl : l.length = 3)

/-! ### R1. `variable` in a `section` · context: a theorem receives exactly the variables its
statement mentions (plus the types they need, here `α`). Not `m`, `x` or `hl` below. -/
theorem r1_demo : l ++ [] = l := by
  simp

/-! ### R2. A `def` in a section; `unfold f` · goal: the name `snoc` applied → its body
`snoc` mentions `l` and `x`, so it takes them as arguments: `snoc : {α : Type} → List α → α → List α`.
Inside the section you still write them, `snoc l x`; there is no automatic `snoc`. -/
def snoc : List α := l ++ [x]

theorem r2_demo (P : List α → Prop) (h : P (l ++ [x])) : P (snoc l x) := by
  unfold snoc
  exact h

/-! ### R4. `simp [f]` · goal: unfolds `f`, applies R3 and other simp lemmas, leaves arithmetic
`[x].length` becomes `1`; `simp` does not reorder `l.length + 1` into `1 + l.length`. -/
theorem r4_demo : (snoc l x).length = 1 + l.length := by
  simp [snoc]
  omega

/-! ### R6. `rfl` · closes an equation whose two sides are equal after unfolding definitions -/
theorem r6_demo : snoc l x = l ++ [x] := by
  rfl

/-! ### R7. `include hl in` · context gains `hl` for the NEXT declaration only, though its statement
never mentions `hl`. After that declaration, `hl` is invisible again. -/
include hl in
theorem r7_demo : 0 < l.length := by
  omega

end RefSec

/-! ## Lists and arithmetic -/

/-! ### R3. `List.length_append` · `(as ++ bs).length = as.length + bs.length` · goal -/
example {α : Type} (p q : List α) (P : Nat → Prop) (h : P (p.length + q.length)) :
    P (p ++ q).length := by
  rw [List.length_append]
  exact h

/-! ### R5. `omega` · closes linear goals over `Nat`/`Int`; any other subterm (`f a b`, `a * b`) is
an opaque unknown. So `f a b + f a b = 2 * f a b` is fine, but `a * b` and `b * a` are two unrelated
unknowns to it. -/
example (f : Nat → Nat → Nat) (a b : Nat) : f a b + f a b = 2 * f a b := by
  omega

/-! ## Proving `≠` -/

/-! ### R8. `intro h` on `a ≠ b` · goal `a ≠ b` → context gains `h : a = b`, goal `False`
`a ≠ b` is `¬ (a = b)`, which is `a = b → False`. -/
example {α : Type} (a b : α) (h' : a = b → False) : a ≠ b := by
  intro h
  exact h' h

/-! ### R9. `List.append_eq_nil_iff` · `p ++ q = [] ↔ p = [] ∧ q = []` · context, via `.mp`
`hiff.mp : A → B` is the left-to-right direction of `hiff : A ↔ B` (`.mpr` is right to left). -/
example {α : Type} (p q : List α) (h : p ++ q = []) (G : Prop) (g : p = [] ∧ q = [] → G) : G := by
  have h2 := List.append_eq_nil_iff.mp h
  exact g h2

/-! ### R10. `h.1`, `h.2` · context: the two halves of `h : A ∧ B` (`And.left`, `And.right`) -/
example (A B G : Prop) (h : A ∧ B) (g : A → G) : G := by
  have ha := h.1
  exact g ha

/-! ### R11. `exact hne hp` · closes `False`: `hne : p ≠ []` is a function from `p = []` to `False` -/
example {α : Type} (p : List α) (hne : p ≠ []) (hp : p = []) : False := by
  exact hne hp

/-! ## Namespaces -/

-- Inside `namespace Rect … end Rect` every new name gets the prefix `Rect.`.
namespace Rect
def perim (w h : Nat) : Nat := 2 * w + 2 * h

theorem perim_comm (w h : Nat) : perim w h = perim h w := by unfold perim; omega

end Rect

/-! ### R12. `rw [Rect.perim_comm b a]` · goal: the full name `Namespace.lemma`, with explicit
arguments so that only `Rect.perim b a` is rewritten (to `Rect.perim a b`) -/
example (a b : Nat) (P : Nat → Prop) (h : P (Rect.perim a b + Rect.perim a b)) :
    P (Rect.perim a b + Rect.perim b a) := by
  rw [Rect.perim_comm b a]
  exact h

/-! ### R13. `open Rect in tac` · the same step with the short name `perim_comm`; the `open` lasts
for this one tactic only -/
example (a b : Nat) (P : Nat → Prop) (h : P (Rect.perim b a + Rect.perim b a)) :
    P (Rect.perim a b + Rect.perim b a) := by
  open Rect in rw [perim_comm a b]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

section WorkSec
variable {α : Type} (l m : List α) (hm : m ≠ [])

/-! ### W1. A section `def`, then `simp [name]` and `omega` (R2, R4, R5) -/
def thrice : List α := l ++ l ++ l

theorem thrice_length : (thrice l).length = 3 * l.length := by
  simp [thrice]
  omega

/-! ### W2. `include` + `≠` on the RIGHT half of an append (R7, R8, R9, R10, R11) -/
include hm in
theorem append_ne_nil_right : l ++ m ≠ [] := by
  intro h
  have h2 := List.append_eq_nil_iff.mp h
  exact hm h2.2

end WorkSec

/-! ### W3. A namespaced commutation lemma, then linear arithmetic (R13, R5) -/
example (a b : Nat) : Rect.perim b a + 2 * Rect.perim a b = 3 * Rect.perim a b := by
  open Rect in rw [perim_comm b a]
  omega

end E056Guide

/- Guide for E050 (Managing hypotheses).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `Q` stand for "the rest of a statement": the step changes only the part shown inside `P (…)`.
In this exercise most steps change the CONTEXT (the hypotheses above `⊢`), not the goal: watch them.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace E050Guide

/-! # Part R · Reference entries -/

/-! ## Instantiating a `∀`-hypothesis -/

/-! ### R1. `have ha := h a` · context gains `ha : P a`; `h : ∀ x, P x` stays
`h a` is `h` applied to `a`: a proof of `∀ x, P x` is a function from `x` to a proof of `P x`. -/
example {α : Type} (P : α → Prop) (a : α) (h : ∀ x, P x) : P a ∧ ∀ x, P x := by
  have ha := h a
  exact ⟨ha, h⟩

/-! ### R2. `specialize h a` · context: `h : ∀ x, P x` is REPLACED by `h : P a` (the `∀` is gone)
Use R1 first for every other instance you still need. -/
example {α : Type} (P : α → Prop) (a : α) (h : ∀ x, P x) : P a := by
  specialize h a
  exact h

/-! ### R3. `rw [h1, h2]` · goal: rewrite with each equation in turn; `rw` then tries `rfl`
After the last rewrite the goal `2 + 4 = 6` is closed by computation, so no tactic follows. -/
example (f : Nat → Nat) (h1 : f 1 = 2) (h2 : f 2 = 4) : f 1 + f 2 = 6 := by
  rw [h1]
  rw [h2]

/-! ## Replacing a hypothesis -/

/-! ### R4. `replace h : T := proof` · context: `h` now has type `T`; the old `h` is gone
`proof` may use the old `h`. Compare `have h' : T := proof`, which keeps both. -/
example {α : Type} (P Q : α → Prop) (a : α) (h : P a) (f : P a → Q a) : Q a := by
  replace h : Q a := f h
  exact h

/-! ### R5. `rw [Nat.zero_add] at h` · context: `h` rewritten; goal unchanged
`Nat.zero_add (n : Nat) : 0 + n = n`. `0 + n` does not compute to `n` (addition recurses on its
SECOND argument), so `exact h` with `h : P (0 + n)` fails against `⊢ P n`: rewrite first. -/
example (P : Nat → Prop) (n : Nat) (h : P (0 + n)) : P n := by
  rw [Nat.zero_add] at h
  exact h

/-! ## Eliminating variables -/

/-! ### R6. `subst h` · context: with `h : x = e` (or `h : e = x`) and `x` a variable not in `e`,
`x` and `h` disappear and every `x` (in the goal and in the other hypotheses) becomes `e`. -/
example {α : Type} (P : α → Prop) (g : α → α) (x y : α) (h : x = g y) (hp : P (g y)) :
    P x := by
  subst h
  exact hp

example {α : Type} (P : α → Prop) (g : α → α) (x y : α) (h : g y = x) (hp : P (g y)) :
    P x := by
  subst h
  exact hp

/- When BOTH sides are variables, `subst h` with `h : x = y` removes the right-hand one, `y`,
and writes `x` in its place. -/
example {α : Type} (P : α → Prop) (x y : α) (h : x = y) (hp : P x) : P y := by
  subst h
  exact hp

/-! ## Rewriting in several hypotheses -/

/-! ### R7. `rw [h] at h1 h2` · context: `h1` and `h2` both rewritten; goal unchanged
`at *` rewrites every hypothesis and the goal. -/
example {α : Type} (P Q : α → Prop) (a b : α) (h : a = b) (h1 : P a) (h2 : Q a) :
    P b ∧ Q b := by
  rw [h] at h1 h2
  exact ⟨h1, h2⟩

/-! ### R8. `exact ⟨ha, hb⟩` · closes `A ∧ B` from `ha : A` and `hb : B` (anonymous constructor) -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  exact ⟨ha, hb⟩

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Two instances of one `∀`: copy one (R1), specialize to the other (R2), rewrite (R3) -/
example (g : Nat → Nat) (h : ∀ n, g n = n + 1) : g 2 * g 5 = 18 := by
  have h2 := h 2
  specialize h 5
  rw [h2, h]

/-! ### W2. A chain of equations, eliminated from the end (R6, three times), then `rfl` -/
example (x y z : Nat) (e1 : x = y) (e2 : y = z) (e3 : z = 2) : x * y = 4 := by
  subst e3
  subst e2
  subst e1
  rfl

/-! ### W3. Clean a hypothesis with R4 + R5, then use it in the goal -/
example (m : Nat) (h : 0 + m = 3) : m + 1 = 4 := by
  replace h : m = 3 := by rw [Nat.zero_add] at h; exact h
  rw [h]

/-! ### W4. `rw [h] at *`: every hypothesis (except `h`) and the goal at once -/
example (a b : Nat) (h : a = b) (h1 : a + 1 = 3) : b + 1 = 3 ∧ a = b := by
  rw [h] at *
  exact ⟨h1, rfl⟩

end E050Guide

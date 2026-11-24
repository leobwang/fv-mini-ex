/- Guide for E051 (Congruence).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
The exercise itself is written as terms (`congrArg F h`, `fun h => …`); each entry shows the term
inside a tactic block (`apply`, `exact`, `have`, `intro`) only so that the infoview has a state to show.
`{α β γ : Type}` are arbitrary types, `F`, `G` arbitrary functions, and a hypothesis `h` in an entry is
only there to finish the example.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/

namespace E051Guide

/-! # Part R · Reference entries -/

/-! ## Pushing an equality through a function -/

/-! ### R1. `congrArg F h` · goal `F a = F b` → `a = b`
`congrArg : (f : α → β) → a₁ = a₂ → f a₁ = f a₂`. As a term, `congrArg F h` proves `F a = F b` from
`h : a = b`. In a tactic block, `apply congrArg F` leaves exactly the argument `a = b` to prove. -/
example {α β : Type} (F : α → β) (a b : α) (h : a = b) : F a = F b := by
  apply congrArg F
  exact h

/-! ### R2. `congrArg (fun x => F x c) h` · the "context" `F` is a lambda around the part that changes
Lean matches `(fun x => F x c) a` with `F a c` by computing the application (β-reduction), so any
expression with a hole `x` can serve as the function. -/
example {α β γ : Type} (F : α → β → γ) (a b : α) (c : β) (h : a = b) : F a c = F b c := by
  apply congrArg (fun x => F x c)
  exact h

/-! ### R3. `(· * k)` · shorthand for `fun x => x * k`
`·` marks the hole; the parentheses delimit the lambda. `(· + 1)` is `fun x => x + 1`. -/
example (x y k : Nat) (h : x = y) : x * k = y * k := by
  apply congrArg (· * k)
  exact h

/-! ## Evaluating an equality of functions -/

/-! ### R4. `congrFun h a` · context gains `f a = g a` from `h : f = g`
`congrFun : f = g → ∀ a, f a = g a`. If `f` and `g` are lambdas, the new fact is printed with both
sides already computed (W3). -/
example {α β : Type} (f g : α → β) (a : α) (h : f = g) : f a = g a := by
  have ha := congrFun h a
  exact ha

/-! ## Proving `≠` -/

/-! ### R5. `intro hab` (term: `fun hab => …`) · goal `a ≠ b` → context `hab : a = b`, goal `False`
`a ≠ b` is notation for `Ne a b`, defined as `a = b → False`, so a proof of it is a function. -/
example {α : Type} (a b : α) (h : a = b → False) : a ≠ b := by
  intro hab
  exact h hab

/-! ### R6. `Nat.succ_ne_self` · `n.succ ≠ n`; applied to `h : k + 1 = k` it closes `False`
`n.succ` (`Nat.succ n`) and `n + 1` compute to the same thing, so `h : k + 1 = k` is accepted as the
argument. -/
example (k : Nat) (h : k + 1 = k) : False := by
  exact Nat.succ_ne_self k h

/-! ## Splitting an equation of applications -/

/-! ### R7. `congr` · goal `F a c e = F b d e` → goals `a = b`, `c = d`
One goal per argument; it closes each new goal it can by `rfl` (here `e = e`) or by a hypothesis of
exactly that type, so with `h : a = b` in the context nothing is left (second example). -/
example {α β γ δ : Type} (F : α → β → γ → δ) (a b : α) (c d : β) (e : γ) (h : a = b ∧ c = d) :
    F a c e = F b d e := by
  congr
  exact h.1
  exact h.2

example {α β : Type} (G : α → α → β) (a b : α) (h : a = b) : G a a = G b b := by
  congr

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R2 then R1: the changing spot sits deep inside, so the lambda covers everything around it -/
example (f : Nat → Nat) (a b : Nat) (h : a = b) : (f a + 1) * 2 = (f b + 1) * 2 := by
  apply congrArg (fun x => (f x + 1) * 2)
  exact h

/-! ### W2. R4 then R3: evaluate a function equality, then push it through `(· * 2)` -/
example (f g : Nat → Nat) (h : f = g) (x : Nat) : f x * 2 = g x * 2 := by
  have hx := congrFun h x
  exact congrArg (· * 2) hx

/-! ### W3. R5, R4, then `Nat.succ_ne_zero : n.succ ≠ 0`: two functions differ at `0` -/
example : (fun n : Nat => 2 * n + 1) ≠ (fun _ => 0) := by
  intro h
  have h0 := congrFun h 0
  exact Nat.succ_ne_zero (2 * 0) h0

/-! ### W4. `congr` goes all the way down; `congr 1` stops after one layer -/
example (F : Nat → Nat) (a b c d : Nat) (h : a = b ∧ c = d) : F (a + c) = F (b + d) := by
  congr
  exact h.1
  exact h.2

example (F : Nat → Nat) (a b c d : Nat) (h : a + c = b + d ∧ True) : F (a + c) = F (b + d) := by
  congr 1
  exact h.1

end E051Guide

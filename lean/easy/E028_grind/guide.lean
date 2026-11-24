/- Guide for E028 (grind).
Part R: one reference entry per kind of fact the exercise hands to `grind`, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`α β : Type` are arbitrary types, `f : α → β` an arbitrary function, `a b c : Nat` and `x y : Int`
arbitrary numbers; hypotheses `h`, `h1`, `h2` are the facts `grind` reads from the context. Every
entry is one step: `grind` closes the goal or fails.
Part W: worked combinations and a few limits, on statements that are NOT the exercise's.
Assumed: E001 (`decide`), E003 (tactic mode), E008 (`¬`, `False`), E010 (`simp`), E011 (`omega`).
-/

namespace E028Guide

/-! # Part R · Reference entries -/

/-! ## Equalities between terms -/

/-! ### R1. `grind` · congruence closure: closes `f a = f c` from a chain of equalities
`grind` puts equal terms in one class (`a`, `b`, `c` here) and then knows that applying the same
function to equal arguments gives equal results. -/
example {α β : Type} (f : α → β) (a b c : α) (h1 : a = b) (h2 : b = c) : f a = f c := by
  grind

/-! ### R2. `grind` · linear arithmetic over `Nat`/`Int`: solves for a variable from the context
The arithmetic module works like `omega` (E011): numerals, `+`, `-`, numeral `*`, `≤ < = ≠`. -/
example (a : Nat) (h : a + 3 = 8) : a = 5 := by
  grind

/-! ### R3. `grind` · an equality found by arithmetic feeds congruence
`x = y` is not in the context; arithmetic derives it from `h`, and congruence then closes `f x = f y`. -/
example {β : Type} (f : Int → β) (x y : Int) (h : x + 1 = y + 1) : f x = f y := by
  grind

/-! ## Order and subtraction -/

/-! ### R4. `grind` · two inequalities that pin a value give an equality -/
example (x y : Int) (h1 : x < y + 1) (h2 : y < x + 1) : x = y := by
  grind

/-! ### R5. `grind` with `Nat` subtraction · closes the goal; truncation handled as in `omega`
`a - 2` on `Nat` is `0` when `a < 2`; `h` rules that case out. -/
example (a b : Nat) (h : a = b + 3) : a - 2 = b + 1 := by
  grind

/-! ### R6. `grind` · ring normalisation: closes an identity of commutative (semi)rings
Both sides are expanded into a sum of monomials and compared, like `ring`. -/
example (x y : Int) : (x - y) * (x + y) = x * x - y * y := by
  grind

/-! ## Case splits and negated goals -/

/-! ### R7. `grind` · splits on `if … then … else …`: tries `p` and `¬ p`, refutes each wrong case
`[Decidable p]` says `p` can be decided, which `if` needs; `n < 5`, `a = b` on `Nat` qualify. -/
example (p : Prop) [Decidable p] (a b : Nat) (h : (if p then a else b) = a) (hab : a ≠ b) : p := by
  grind

/-! ### R8. `grind` · works by contradiction: assumes the negated goal, uses `≠` facts
Here it adds `¬ a = 2` and combines it with `h1`, `h2`, `h3` to reach `False`. -/
example (a : Nat) (h1 : a < 3) (h2 : a ≠ 0) (h3 : a ≠ 1) : a = 2 := by
  grind

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R5 then R1: a subtraction made exact, then congruence through two functions -/
example (f g : Nat → Nat) (a b : Nat) (h : a = b + 2) : g (f (a - 2)) = g (f b) := by
  grind

/-! ### W2. substitution then R6: `h` replaces `x`, ring normalisation checks the rest -/
example (x y : Int) (h : x = y + 1) : x * x = y * y + 2 * y + 1 := by
  grind

/-! ### W3. R7 inside a hypothesis about `f`: the `if` is split, each branch is linear (R2) -/
example (f : Nat → Nat) (a : Nat) (hf : f a = if a = 0 then 1 else 2 * a) (h : f a = 6) :
    a = 3 := by
  grind

/-! ### W4. `grind` instantiates a `∀` hypothesis at the terms it sees (here `x := 2`) -/
example (f : Nat → Nat) (hf : ∀ x, f x = x + 1) : f 2 = 3 := by
  grind

end E028Guide

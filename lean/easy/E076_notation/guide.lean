/- Guide for E076 (Notation).
Part R: one reference entry per command, tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The notation entries (R1–R6) show how a term groups by rewriting with `e : <subterm> = d`: `rw [e]`
succeeds only when `<subterm>` really is a subterm, so the after-state reveals the parse.
Part W: worked combinations on objects that are NOT the exercise's (other tokens, another `def`).
Assumed: Lean basics (E001–E033).
-/

namespace E076Guide

/-! # Part R · Reference entries -/

/-! ## Declaring an infix operator: associativity and level -/

-- The infix operators of this guide (they are global once declared, like the exercise's).
infixl:65 " +' " => Nat.add
infixr:75 " ^' " => Nat.pow

/-! ### R1. `infixl:65 " +' " => Nat.add` · parse: `a +' b +' c` is `(a +' b) +' c`
`rw [e]` with `e : a +' b = d` finds `a +' b` inside the goal, so it is a subterm. -/
example (P : Nat → Prop) (a b c d : Nat) (e : a +' b = d) (h : P (d +' c)) : P (a +' b +' c) := by
  rw [e]
  exact h

/-! ### R2. `infixr:75 " ^' " => Nat.pow` · parse: `a ^' b ^' c` is `a ^' (b ^' c)` -/
example (P : Nat → Prop) (a b c d : Nat) (e : b ^' c = d) (h : P (a ^' d)) : P (a ^' b ^' c) := by
  rw [e]
  exact h

/-! ### R3. Level below `*` (70) · parse: `a +' b * c` is `a +' (b * c)` -/
example (P : Nat → Prop) (a b c d : Nat) (e : b * c = d) (h : P (a +' d)) : P (a +' b * c) := by
  rw [e]
  exact h

/-! ### R4. Same level as `+` and `-` (65), left grouping · mixed chains group left
`a + b +' c` is `(a + b) +' c` and `a +' b + c` is `(a +' b) + c`. -/
example (P : Nat → Nat → Prop) (a b c d₁ d₂ : Nat) (e₁ : a + b = d₁) (e₂ : a +' b = d₂)
    (h : P (d₁ +' c) (d₂ + c)) : P (a + b +' c) (a +' b + c) := by
  rw [e₁, e₂]
  exact h

/-! ### R5. `set_option pp.notation false in` · display: the infoview prints the plain term
`x.add y` is field notation for `Nat.add x y`; `+` itself prints as `HAdd.hAdd`. -/
set_option pp.notation false in
example (P : Nat → Prop) (a b c : Nat) (h : P (Nat.add (Nat.add a b) c)) : P (a +' b +' c) := by
  exact h

/-! ## Mixfix notation -/

/-! ### R6. `notation "⌈" a "⌉²" => Nat.mul a a` · parse: `⌈x⌉²` is `Nat.mul x x`
Any tokens may surround the arguments, and an argument may be used twice. A notation that repeats
an argument is not printed back: the infoview shows its expansion, here `x.mul x`. -/
notation "⌈" a "⌉²" => Nat.mul a a

example (P : Nat → Prop) (x d : Nat) (e : Nat.mul x x = d) (h : P d) : P ⌈x⌉² := by
  rw [e]
  exact h

/-! ## Seeing through notation in a proof -/

def cross (a b : Nat × Nat) : Nat := a.1 * b.2 + a.2 * b.1
infixl:70 " ⊗ " => cross

/-! ### R7. `simp only [cross]` (or `unfold cross`) · goal: a `def` behind an infix → its body
Notation is only syntax: `a ⊗ b` is the term `cross a b`, so unfolding `cross` removes the `⊗`.
`a.fst`, `a.snd` are `a.1`, `a.2`. -/
example (P : Nat → Prop) (a b : Nat × Nat) (h : P (a.1 * b.2 + a.2 * b.1)) : P (a ⊗ b) := by
  simp only [cross]
  exact h

/-! ### R8. `Nat.mul_comm` · `∀ (n m : Nat), n * m = m * n` · goal: swap the factors of a product
Inside `simp [..., Nat.mul_comm]` it is used as a permutation lemma (it rewrites only when the result is
smaller in an internal order), so it does not loop. -/
example (P : Nat → Prop) (a b : Nat) (h : P (b * a)) : P (a * b) := by
  rw [Nat.mul_comm]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The wrong associativity at the right level: `infixr:65` swallows a following `+`
`a -' b + c` is `a -' (b + c)`, so `rw` finds `b + c`. -/
infixr:65 " -' " => Nat.sub

example (P : Nat → Prop) (a b c d : Nat) (e : b + c = d) (h : P (a -' d)) : P (a -' b + c) := by
  rw [e]
  exact h

/-! ### W2. Unfold, then normalise products and sums with commutativity lemmas: R7, R8 -/
example (a b : Nat × Nat) : a ⊗ b = b ⊗ a := by
  simp only [cross]
  simp [Nat.mul_comm, Nat.add_comm]

end E076Guide

/- Guide for M055 (Primes and products).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `g` or `h` in an entry is only there to finish the example; it shows what the state became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

namespace M055Guide

/-! # Part R · Reference entries -/

/-! ## Squares as products -/

/-! ### R1. `rw [pow_two] at h` · context: `h` about `a ^ 2` → `h` about `a * a`
`pow_two a : a ^ 2 = a * a` (for any monoid, e.g. `ℕ`). `at h` rewrites the hypothesis, not the goal. -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (G : Prop) (g : P (a * a) → G)
    (h : P (a ^ 2)) : G := by
  rw [pow_two] at h
  exact g h

/-! ## Euclid's lemma and case splits -/

/-! ### R2. `Nat.Prime.dvd_mul` · context gains `p ∣ m ∨ p ∣ n`
`Nat.Prime.dvd_mul : p.Prime → (p ∣ m * n ↔ p ∣ m ∨ p ∣ n)`. With `hp : p.Prime`, `hp.dvd_mul` is
that `↔`, and `.mp` is its left-to-right direction, a function from `p ∣ m * n` to the disjunction. -/
example (p m n : ℕ) (hp : p.Prime) (h : p ∣ m * n) (G : Prop) (g : p ∣ m ∨ p ∣ n → G) : G := by
  have h' := hp.dvd_mul.mp h
  exact g h'

/-! ### R3. `rcases h with h | h` · goal list: one goal → one goal per side of `h : A ∨ B`
In each new goal, `h` is the proof of that side; `·` focuses one goal. `rcases e with h | h` also works
on a term `e`. -/
example (A B G : Prop) (h : A ∨ B) (ga : A → G) (gb : B → G) : G := by
  rcases h with h | h
  · exact ga h
  · exact gb h

/-! ## Reusing a theorem and products of divisibilities -/

/-! ### R4. `have hu := thm n hn` · context gains `hu : U n`
An earlier theorem is a function: give it its explicit arguments and it returns its conclusion. -/
example (T U : ℕ → Prop) (thm : ∀ n, T n → U n) (n : ℕ) (hn : T n) (G : Prop) (g : U n → G) :
    G := by
  have hu := thm n hn
  exact g hu

/-! ### R5. `rw [pow_two]` on the goal · goal: rewrites ONE base
`rw` fixes `a` at the first match `x ^ 2`, then rewrites only `x ^ 2`; `y ^ 2` needs a second
`pow_two`. Write `rw [pow_two, pow_two]`. -/
example {M : Type} [Monoid M] (x y : M) (P : M → M → Prop) (h : P (x * x) (y * y)) :
    P (x ^ 2) (y ^ 2) := by
  rw [pow_two]
  rw [pow_two]
  exact h

/-! ### R6. `mul_dvd_mul` · closes `a * c ∣ b * d`
`mul_dvd_mul : a ∣ b → c ∣ d → a * c ∣ b * d` (for any commutative semigroup, e.g. `ℕ`). -/
example {α : Type} [CommSemigroup α] (a b c d : α) (hab : a ∣ b) (hcd : c ∣ d) :
    a * c ∣ b * d := by
  exact mul_dvd_mul hab hcd

/-! ## Proving a disjunction -/

/-! ### R7. `Or.inl`, `Or.inr` · closes `A ∨ B ∨ C` from a proof of one side
`∨` nests to the right: `A ∨ B ∨ C` is `A ∨ (B ∨ C)`. So `A` is `Or.inl _`, `B` is
`Or.inr (Or.inl _)`, `C` is `Or.inr (Or.inr _)`. -/
example (A B C : Prop) (ha : A) : A ∨ B ∨ C := by
  exact Or.inl ha

example (A B C : Prop) (hb : B) : A ∨ B ∨ C := by
  exact Or.inr (Or.inl hb)

example (A B C : Prop) (hc : C) : A ∨ B ∨ C := by
  exact Or.inr (Or.inr hc)

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Euclid's lemma, then each branch into a swapped disjunction: R2, R3, R7 -/
example (p a b : ℕ) (hp : p.Prime) (h : p ∣ a * b) : p ∣ b ∨ p ∣ a := by
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-! ### W2. A square on one side only: R5, then R6 -/
example (p a b : ℕ) (ha : p ∣ a) (hb : p ∣ b) : p ^ 2 ∣ a * b := by
  rw [pow_two]
  exact mul_dvd_mul ha hb

/-! ### W3. Ruling out a branch: `absurd : A → ¬A → B` closes any goal from a contradiction -/
example (p a b : ℕ) (hp : p.Prime) (h : p ∣ a * b) (hb : ¬ p ∣ b) : p ∣ a := by
  rcases hp.dvd_mul.mp h with h | h
  · exact h
  · exact absurd h hb

end M055Guide

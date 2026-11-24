/- Guide for E092 (zify and lift).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `Q` stand for "the rest of a goal or hypothesis": the step changes only the part shown inside
`P (…)`. A hypothesis `g` or `h` in an entry is only there to finish the example; it shows what the
goal became.
`↑a` with `a : ℕ` in an `ℤ` statement is `Nat.cast a`, the natural number `a` seen as an integer.
Part W: worked combinations on other expressions.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E092Guide

/-! # Part R · Reference entries -/

/-! ## Truncated ℕ subtraction → ℤ -/

/-! ### R1. `Nat.one_le_pow` · `(n m : ℕ) → 0 < m → 1 ≤ m ^ n`; in a `have`, context gains the fact
In ℕ, `0 < m` is by definition `1 ≤ m`, so a hypothesis `1 ≤ m` is accepted as the argument (W3). -/
example (m k : ℕ) (hm : 0 < m) (G : Prop) (g : 1 ≤ m ^ k → G) : G := by
  have hp : 1 ≤ m ^ k := Nat.one_le_pow k m hm
  exact g hp

/-! ### R2. `zify [hb]` · goal: a ℕ (in)equation → the same over ℤ, `↑(a - b)` → `↑a - ↑b` by `hb : b ≤ a`
Without `hb` the cast stays as `↑(a - b)` (W2): ℕ subtraction truncates at 0. -/
example (a b c d : ℕ) (hb : b ≤ a) (h : (a : ℤ) - b + c = d) : a - b + c = d := by
  zify [hb]
  exact h

/-! ### R3. `ring` · closes a commutative-ring identity in ℤ; each `↑a` counts as one unknown -/
example (a b c : ℕ) : ((a : ℤ) - b) * c = a * c - b * c := by
  ring

/-! ## A nonnegative integer → a natural number -/

/-! ### R4. `lift x to ℕ using hx` · context: `x : ℤ` becomes `x : ℕ`, `hx : 0 ≤ x` is used up;
every old `x` (goal and hypotheses) now reads `↑x`. -/
example (x : ℤ) (hx : 0 ≤ x) (P Q : ℤ → Prop) (hq : Q x) (h : ∀ n : ℕ, Q ↑n → P ↑n) : P x := by
  lift x to ℕ using hx
  exact h x hq

/-! ### R5. `norm_cast at h h1 ⊢` · context and goal: the casts are pulled out and dropped
Integer numerals count as casts: `(10 : ℤ)` is read as `↑(10 : ℕ)`. `↑a ≠ 2` comes out as `¬a = 2`. -/
example (a : ℕ) (h : (a : ℤ) ∣ 10) (h1 : (a : ℤ) ≠ 2) (g : a ∣ 10 → a ≠ 2 → a = 10) :
    (a : ℤ) = 10 := by
  norm_cast at h h1 ⊢
  exact g h h1

/-! ## Divisors of a prime -/

/-! ### R6. `Nat.dvd_prime` · `Nat.Prime p → (m ∣ p ↔ m = 1 ∨ m = p)`; `.mp` uses the `↔` left to right
In a `have`, the context gains the disjunction. -/
example (p m : ℕ) (hp : p.Prime) (h : m ∣ p) (G : Prop) (g : m = 1 ∨ m = p → G) : G := by
  have h' := (Nat.dvd_prime hp).mp h
  exact g h'

/-! ### R7. `norm_num` · closes `Nat.Prime n` for a numeral `n` -/
example : Nat.Prime 11 := by norm_num

/-! ### R8. `Or.resolve_left` · `A ∨ B → ¬A → B`; `h.resolve_left hna` closes the goal `B` -/
example (A B : Prop) (h : A ∨ B) (hna : ¬A) : B := by
  exact h.resolve_left hna

/-! # Part W · Worked combinations (not the exercise's expressions) -/

/-! ### W1. Two subtractions need two facts: `zify [hb, hd]` (R2), then `ring` (R3) -/
example (a b c d : ℕ) (hb : b ≤ a) (hd : d ≤ c) : (a - b) + (c - d) + b + d = a + c := by
  zify [hb, hd]
  ring

/-! ### W2. `zify` with no fact leaves the truncated subtraction under one cast -/
example (a b c d : ℕ) (h : ((a - b : ℕ) : ℤ) + c = d) : a - b + c = d := by
  zify
  exact h

/-! ### W3. A fact for the power first (R1, fed `1 ≤ m`), then R2, R3 -/
example (m : ℕ) (hm : 1 ≤ m) : (m ^ 3 - 1) + 1 = m ^ 3 := by
  have hp : 1 ≤ m ^ 3 := Nat.one_le_pow 3 m hm
  zify [hp]
  ring

/-! ### W4. Lift, strip the casts (R4, R5), then `omega` finishes in ℕ -/
example (x : ℤ) (hx : 0 ≤ x) (h : x < 3) (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  lift x to ℕ using hx
  norm_cast at h h0 h1 ⊢
  omega

/-! ### W5. Divisors of 13 (R6 with R7 for the side goal), the other case ruled out by `Or.resolve_right`
`Or.resolve_right : A ∨ B → ¬B → A` is R8 for the right-hand case. -/
example (m : ℕ) (h : m ∣ 13) (h13 : m ≠ 13) : m = 1 := by
  have h' := (Nat.dvd_prime (by norm_num)).mp h
  exact h'.resolve_right h13

end E092Guide

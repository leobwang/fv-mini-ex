/- Guide for M064 (Infinitely many primes ≡ 1 mod 4).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G` is
an arbitrary goal. A hypothesis `h` in an entry is only there to finish the example; it shows what
the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`m.factorial + 1`, `a ^ 3 + 2`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M064Guide

/-! # Part R · Reference entries -/

/-! ## Getting a prime factor -/

/-! ### R1. `Nat.factorial_pos` · context gains `0 < n.factorial`
`Nat.factorial_pos n : 0 < n.factorial`. `n.factorial` is `n!`. -/
example (n : ℕ) (G : Prop) (h : 0 < n.factorial → G) : G := by
  have hf := Nat.factorial_pos n
  exact h hf

/-! ### R2. `obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := m) hm` · context gains `p`, `hp`, `hpd`
`Nat.exists_prime_and_dvd : n ≠ 1 → ∃ p, Nat.Prime p ∧ p ∣ n` (`n` implicit; `(n := m)` names it). -/
example (m : ℕ) (hm : m ≠ 1) (G : Prop) (h : ∀ p, Nat.Prime p → p ∣ m → G) : G := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := m) hm
  exact h p hp hpd

/-! ### R3. `nlinarith` · closes a (non)linear arithmetic goal over an ordered ring, using hypotheses
It multiplies pairs of hypotheses; `≠` goals are fine. Needs `0 < a` from the context. -/
example (a : ℕ) (ha : 0 < a) : (3 * a) ^ 2 + 2 ≠ 2 := by
  nlinarith

/-! ## Squares in `ZMod p` -/

/-! ### R4. `haveI := Fact.mk hp` · context gains the instance `this : Fact (Nat.Prime p)`
`Fact.mk : P → Fact P`. Lemmas with a `[Fact (Nat.Prime p)]` argument find it by themselves. -/
example (p : ℕ) (hp : Nat.Prime p) (G : Prop) (h : [Fact (Nat.Prime p)] → G) : G := by
  haveI := Fact.mk hp
  exact h

/-! ### R5. `rw [eq_neg_iff_add_eq_zero]` · goal `a = -b` → `a + b = 0` -/
example {α : Type} [AddGroup α] (a b : α) (h : a + b = 0) : a = -b := by
  rw [eq_neg_iff_add_eq_zero]
  exact h

/-! ### R6. `ZMod.natCast_eq_zero_iff` · `(↑a : ZMod b) = 0 ↔ b ∣ a`; `.mpr` turns `b ∣ a` into `↑a = 0` -/
example (a p : ℕ) (hd : p ∣ a) (G : Prop) (h : (a : ZMod p) = 0 → G) : G := by
  have h0 := (ZMod.natCast_eq_zero_iff a p).mpr hd
  exact h h0

/-! ### R7. `exact_mod_cast e` · closes the goal with `e` after moving casts `↑` through `+`, `*`, `^`
Here `h` casts the whole ℕ expression; the goal casts only `a`. -/
example (a p : ℕ) (h : ((a ^ 3 + 2 : ℕ) : ZMod p) = 0) : (a : ZMod p) ^ 3 + 2 = 0 := by
  exact_mod_cast h

/-! ### R8. `ZMod.mod_four_ne_three_of_sq_eq_neg_one` · context gains `p % 4 ≠ 3`
`[Fact (Nat.Prime p)] → y ^ 2 = -1 → p % 4 ≠ 3` for `y : ZMod p` (−1 is a square mod `p`). -/
example (p : ℕ) [Fact (Nat.Prime p)] (y : ZMod p) (hy : y ^ 2 = -1) (G : Prop)
    (h : p % 4 ≠ 3 → G) : G := by
  have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hy
  exact h h3

/-! ## Ruling out `p = 2` -/

/-! ### R9. `rintro rfl` · goal `p ≠ 2` → `False`, with `p` replaced by `2` everywhere -/
example (p : ℕ) (Q : ℕ → Prop) (h : ¬Q 2) (hp : Q p) : p ≠ 2 := by
  rintro rfl
  exact h hp

/-! ### R10. `⟨c, proof⟩` for `k ∣ b` · `k ∣ b` means `∃ c, b = k * c`; goal → `b = k * c` -/
example (k m : ℕ) : k ∣ (k * m) ^ 2 := by
  refine ⟨k * m ^ 2, ?_⟩
  ring

/-! ### R11. `omega` · closes linear goals over ℕ/ℤ with `%`, `/` and `∣` by numerals
A term it cannot read linearly, such as `y ^ 2`, is treated as one opaque number. -/
example (y : ℕ) (h1 : 3 ∣ y ^ 2) (h2 : 3 ∣ y ^ 2 + 1) : False := by
  omega

example (x : ℕ) (h : x % 2 = 1) (h' : x % 4 ≠ 1) : x % 4 = 3 := by
  omega

/-! ## The prime is large -/

/-! ### R12. `refine ⟨x, ?_, hq, ?_⟩` · goal `∃ y, P y ∧ Q y ∧ R y` → goals `P x`, `R x` -/
example (P Q R : ℕ → Prop) (x : ℕ) (hq : Q x) (hp : P x) (hr : R x) : ∃ y, P y ∧ Q y ∧ R y := by
  refine ⟨x, ?_, hq, ?_⟩
  exact hp
  exact hr

/-! ### R13. `by_contra hle` · goal `G` → `False`, context gains `hle : ¬G` -/
example (a b : ℕ) (h : ¬a < b → False) : a < b := by
  by_contra hle
  exact h hle

/-! ### R14. `push Not at hle` · hypothesis: pushes `¬` inward, `¬a < b` → `b ≤ a` -/
example (a b : ℕ) (hle : ¬a < b) (h : b ≤ a → False) : False := by
  push Not at hle
  exact h hle

/-! ### R15. `Nat.Prime.pos`, `Nat.Prime.one_lt` · from `hp : Nat.Prime p`: `hp.pos : 0 < p`, `hp.one_lt : 1 < p` -/
example (p : ℕ) (hp : Nat.Prime p) (G : Prop) (h : 0 < p → 1 < p → G) : G := by
  have h0 := hp.pos
  have h1 := hp.one_lt
  exact h h0 h1

/-! ### R16. `Nat.dvd_factorial` · `0 < m → m ≤ n → m ∣ n.factorial`; `apply` → two goals -/
example (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) : m ∣ n.factorial := by
  apply Nat.dvd_factorial
  exact hm
  exact hmn

/-! ### R17. `dvd_mul_of_dvd_right` · `a ∣ b → ∀ c, a ∣ c * b`; goal `a ∣ c * b` → `a ∣ b` -/
example {α : Type} [CommSemigroup α] (a b c : α) (h : a ∣ b) : a ∣ c * b := by
  apply dvd_mul_of_dvd_right
  exact h

/-! ### R18. `dvd_pow`, `two_ne_zero` · `a ∣ b → n ≠ 0 → a ∣ b ^ n`; `two_ne_zero : 2 ≠ 0` -/
example {α : Type} [Monoid α] (a b : α) (n : ℕ) (h : a ∣ b) (hn : n ≠ 0) : a ∣ b ^ n := by
  apply dvd_pow
  exact h
  exact hn

example {α : Type} [Monoid α] (a b : α) (h : a ∣ b) : a ∣ b ^ 2 := dvd_pow h two_ne_zero

/-! ### R19. `Nat.dvd_add_right` · `k ∣ m → (k ∣ m + n ↔ k ∣ n)`; `.mp` drops the divisible summand -/
example (k m n : ℕ) (hm : k ∣ m) (hk : k ∣ m + n) (G : Prop) (h : k ∣ n → G) : G := by
  have h1 := (Nat.dvd_add_right hm).mp hk
  exact h h1

/-! ### R20. `Nat.dvd_one` · `n ∣ 1 ↔ n = 1`; `.mp` gives `n = 1` -/
example (p : ℕ) (hd : p ∣ 1) (G : Prop) (h : p = 1 → G) : G := by
  have h1 := Nat.dvd_one.mp hd
  exact h h1

/-! ### R21. `.ne'` (`LT.lt.ne'`) · `b < a → a ≠ b`; and `a ≠ b` is `a = b → False` -/
example (p : ℕ) (hlt : 1 < p) (h1 : p = 1) : False := by
  have hne := hlt.ne'
  exact hne h1

/-! ## The residue mod 4 -/

/-! ### R22. `rcases hp.eq_two_or_odd with h | h` · goal list: one goal per side of `∨`
`Nat.Prime.eq_two_or_odd : Nat.Prime p → p = 2 ∨ p % 2 = 1`. -/
example (p : ℕ) (hp : Nat.Prime p) (G : Prop) (h2 : p = 2 → G) (ho : p % 2 = 1 → G) : G := by
  rcases hp.eq_two_or_odd with h | h
  exact h2 h
  exact ho h

/-! ### R23. `absurd` · `absurd : a → ¬a → b`: closes any goal from a fact and its negation -/
example (A G : Prop) (ha : A) (hna : ¬A) : G := by
  exact absurd ha hna

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. From `p ∣ a ^ 3 + 2` to an equation in `ZMod p`: R6, R5, R7 -/
example (a p : ℕ) (hd : p ∣ a ^ 3 + 2) : (a : ZMod p) ^ 3 = -2 := by
  rw [eq_neg_iff_add_eq_zero]
  exact_mod_cast (ZMod.natCast_eq_zero_iff _ p).mpr hd

/-! ### W2. Euclid: a prime factor of `m.factorial + 1` is larger than `m`: R13–R16, R19–R21 -/
example (m p : ℕ) (hp : Nat.Prime p) (hd : p ∣ m.factorial + 1) : m < p := by
  by_contra hle
  push Not at hle
  have h1 : p ∣ m.factorial := Nat.dvd_factorial hp.pos hle
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hd))

end M064Guide

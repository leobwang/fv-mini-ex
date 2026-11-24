/- Guide for H031 (Bézout and Euclid's lemma).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `g` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on facts that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H031Guide

/-! # Part R · Reference entries -/

/-! ## One Euclid step: gcd, `%`, `/` and casts ℕ → ℤ -/

/-! ### R1. `Nat.gcd_rec` · `gcd m n = gcd (n % m) m` · goal: one step of Euclid's algorithm
Lean prints `Nat.gcd m n` as `m.gcd n`. -/
example (m n : ℕ) (P : ℕ → Prop) (h : P (Nat.gcd (n % m) m)) : P (Nat.gcd m n) := by
  rw [Nat.gcd_rec m n]
  exact h

/-! ### R2. `eq_sub_iff_add_eq` · `a = b - c ↔ a + c = b` · goal: a subtraction → an addition -/
example {G : Type} [AddGroup G] (a b c : G) (h : a + c = b) : a = b - c := by
  rw [eq_sub_iff_add_eq]
  exact h

/-! ### R3. `Nat.mod_add_div` · `m % k + k * (m / k) = m` · context gains the division identity -/
example (m k : ℕ) (G : Prop) (g : m % k + k * (m / k) = m → G) : G := by
  have h := Nat.mod_add_div m k
  exact g h

/-! ### R4. `exact_mod_cast e` · closes a goal in ℤ from a fact `e` in ℕ that differs only by casts
It moves `↑` through `+`, `*`, `∣`, numerals on both sides, then compares. -/
example (m k : ℕ) (h : m % k + k * (m / k) = m) :
    ((m % k : ℕ) : ℤ) + (k : ℤ) * ((m / k : ℕ) : ℤ) = (m : ℤ) := by
  exact_mod_cast h

example (d u v : ℕ) (h : d ∣ u + v) : (d : ℤ) ∣ (u : ℤ) + (v : ℤ) := by
  exact_mod_cast h

/-! ### R5. `ring` · closes a commutative-ring identity; a cast such as `↑(m / k)` is an unknown -/
example (m k : ℕ) (x : ℤ) :
    x * ((m : ℤ) - (k : ℤ) * ((m / k : ℕ) : ℤ)) + x * (k : ℤ) * ((m / k : ℕ) : ℤ) = x * m := by
  ring

/-! ## Induction along Euclid's algorithm -/

/-! ### R6. `induction a, b using Nat.gcd.induction` · goal → two goals: `Q 0 n`, and `Q m n` from `Q (n % m) m`
Without `with`, Lean invents the names (`n✝`, `a✝`); `case H1 m n hm ih => …` (or
`induction … with | H0 n => … | H1 m n hm ih => …`) names them. -/
example (Q : ℕ → ℕ → Prop) (h0 : ∀ n, Q 0 n) (h1 : ∀ m n, 0 < m → Q (n % m) m → Q m n)
    (a b : ℕ) : Q a b := by
  induction a, b using Nat.gcd.induction
  case H0 n => exact h0 n
  case H1 m n hm ih => exact h1 m n hm ih

/-! ### R7. `refine ⟨u, v, ?_⟩` · goal `∃ x y, Q x y` → `Q u v` (you choose the witnesses) -/
example {α : Type} (Q : α → α → Prop) (u v : α) (h : Q u v) : ∃ x y, Q x y := by
  refine ⟨u, v, ?_⟩
  exact h

/-! ### R8. `Nat.gcd_zero_left` · `gcd 0 n = n` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Nat.gcd 0 n) := by
  rw [Nat.gcd_zero_left]
  exact h

/-! ### R9. `simp` · goal: clears `0 * _`, `1 * _`, `_ + 0`, `↑0`, `gcd 0 n` (R8) in one call -/
example (n : ℕ) (z : ℤ) (h : z = n) : 0 * ((0 : ℕ) : ℤ) + 1 * z = ((Nat.gcd 0 n : ℕ) : ℤ) := by
  simp
  exact h

/-! ### R10. `obtain ⟨x, y, h⟩ := ih` · context: `ih : ∃ x y, Q x y` → `x y` and `h : Q x y` -/
example {α : Type} (Q : α → α → Prop) (G : Prop) (ih : ∃ x y, Q x y) (g : ∀ x y, Q x y → G) :
    G := by
  obtain ⟨x, y, h⟩ := ih
  exact g x y h

/-! ## Primes and the gcd -/

/-! ### R11. `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right` · context gains `gcd m n ∣ m`, `gcd m n ∣ n` -/
example (m n : ℕ) (G : Prop) (g : Nat.gcd m n ∣ m → Nat.gcd m n ∣ n → G) : G := by
  have hl := Nat.gcd_dvd_left m n
  have hr := Nat.gcd_dvd_right m n
  exact g hl hr

/-! ### R12. `Nat.Prime.eq_one_or_self_of_dvd` · `p.Prime → ∀ d, d ∣ p → d = 1 ∨ d = p` · context
With `hp : p.Prime`, write it `hp.eq_one_or_self_of_dvd d hd`. -/
example (p d : ℕ) (hp : p.Prime) (hd : d ∣ p) (G : Prop) (g : d = 1 ∨ d = p → G) : G := by
  have h := hp.eq_one_or_self_of_dvd d hd
  exact g h

/-! ### R13. `rcases h with h1 | h1` · goal list: `h : A ∨ B` → one goal with `h1 : A`, one with `h1 : B` -/
example (A B G : Prop) (h : A ∨ B) (ga : A → G) (gb : B → G) : G := by
  rcases h with h1 | h1
  · exact ga h1
  · exact gb h1

/-! ### R14. `h ▸ e` · a term: `e : P a` and `h : a = b` give `P b` (rewrite inside the type of `e`) -/
example (a b c : ℕ) (h : a = b) (e : a ∣ c) (G : Prop) (g : b ∣ c → G) : G := by
  have e' : b ∣ c := h ▸ e
  exact g e'

/-! ### R15. `absurd ha hna` · closes any goal from `ha : A` and `hna : ¬A` -/
example (A G : Prop) (ha : A) (hna : ¬A) : G := by
  exact absurd ha hna

/-! ## Divisibility by hand -/

/-! ### R16. `obtain ⟨c, hc⟩ := h` · context: `h : d ∣ n` → `c` and `hc : n = d * c` -/
example (d n : ℤ) (G : Prop) (h : d ∣ n) (g : ∀ c, n = d * c → G) : G := by
  obtain ⟨c, hc⟩ := h
  exact g c hc

/-! ### R17. `refine ⟨c, ?_⟩` · goal `d ∣ n` → `n = d * c` (you choose the quotient `c`) -/
example (d n c : ℤ) (h : n = d * c) : d ∣ n := by
  refine ⟨c, ?_⟩
  exact h

/-! ### R18. `calc` · closes `a = d` by a chain `a = b`, `_ = c`, `_ = d`, each step with its own proof -/
example (a b c d : ℤ) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  calc a = b := h1
    _ = c := h2
    _ = d := h3

/-! ### R19. `one_mul` · `1 * a = a` · goal -/
example {M : Type} [MulOneClass M] (a : M) (P : M → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ## Case split, `∨`, and casts back to ℕ -/

/-! ### R20. `by_cases hA : A` · goal list: one goal with `hA : A`, one with `hA : ¬A` -/
example (A G : Prop) (g1 : A → G) (g2 : ¬A → G) : G := by
  by_cases hA : A
  · exact g1 hA
  · exact g2 hA

/-! ### R21. `right` (and `left`, `Or.inl`) · goal `A ∨ B` → `B`
`left` gives `A`; `exact Or.inl ha` closes `A ∨ B` from `ha : A` in one step. -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R22. `rw [hk] at hz`, `rw [Nat.cast_one] at hz` · context: rewrite a hypothesis; `((1 : ℕ) : ℤ) = 1` -/
example (k : ℕ) (z : ℤ) (G : Prop) (hk : k = 1) (hz : z = (k : ℤ)) (g : z = 1 → G) : G := by
  rw [hk] at hz
  rw [Nat.cast_one] at hz
  exact g hz

/-! ### R23. `Int.natCast_dvd_natCast` · `(↑m : ℤ) ∣ ↑n ↔ m ∣ n` · `.mp` takes divisibility back to ℕ -/
example (m n : ℕ) (G : Prop) (h : (m : ℤ) ∣ (n : ℤ)) (g : m ∣ n → G) : G := by
  have h' := Int.natCast_dvd_natCast.mp h
  exact g h'

/-! # Part W · Worked combinations (not the exercise's facts) -/

/-! ### W1. `m / k` restated in ℤ with the sibling lemma `Nat.div_add_mod'` (`m / k * k + m % k = m`):
R2, then R4. -/
example (m k : ℕ) : ((m / k : ℕ) : ℤ) * (k : ℤ) = (m : ℤ) - ((m % k : ℕ) : ℤ) := by
  rw [eq_sub_iff_add_eq]
  exact_mod_cast Nat.div_add_mod' m k

/-! ### W2. A common divisor divides every integer combination: R16 twice, R17, R18 with R5 -/
example (d a b x y : ℤ) (ha : d ∣ a) (hb : d ∣ b) : d ∣ x * a + y * b := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  refine ⟨x * s + y * t, ?_⟩
  calc x * a + y * b = x * (d * s) + y * (d * t) := by rw [hs, ht]
    _ = d * (x * s + y * t) := by ring

/-! ### W3. A divisor of a prime other than 1 is the prime: R12, R13, R15 -/
example (p d : ℕ) (hp : p.Prime) (hd : d ∣ p) (hd1 : d ≠ 1) : d = p := by
  rcases hp.eq_one_or_self_of_dvd d hd with h1 | h1
  · exact absurd h1 hd1
  · exact h1

/-! ### W4. Induction along Euclid's algorithm with the names given by `with` (R6):
`gcd m n` divides `m` and `n`, proved again without the library lemmas R11. -/
example (a b : ℕ) : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b := by
  induction a, b using Nat.gcd.induction with
    | H0 n => simp
    | H1 m n hm ih =>
      rw [Nat.gcd_rec m n]
      refine ⟨ih.2, ?_⟩
      have e := Nat.dvd_add ih.1 (Dvd.dvd.mul_right ih.2 (n / m))
      rwa [Nat.mod_add_div n m] at e

end H031Guide

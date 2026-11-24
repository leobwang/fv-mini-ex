/- Guide for M065 (Infinitely many primes ≡ 3 mod 4).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. A hypothesis `g` or `h` in an entry is only there to finish the example; it shows
what the goal or context became.
Part W: worked combinations on objects that are NOT the exercise's (residues mod 3, Euclid's `n! + 1`).
Assumed: Lean basics.
-/
import Mathlib

namespace M065Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · residues: a finite case check -/

/-! ### R1. `rw [Nat.mul_mod] at h` · context: `h` about `a * b % n` → about the residues
`Nat.mul_mod : a * b % n = a % n * (b % n) % n`. `at h` rewrites the hypothesis, not the goal. -/
example (a b n : ℕ) (P : ℕ → Prop) (h : P (a * b % n)) : P (a % n * (b % n) % n) := by
  rw [Nat.mul_mod] at h
  exact h

/-! ### R2. `Nat.mod_lt` · context gains the bound `a % n < n`
`Nat.mod_lt : ∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y`. With a numeral, prove `0 < 4` by `(by norm_num)`. -/
example (a n : ℕ) (hn : 0 < n) (G : Prop) (g : a % n < n → G) : G := by
  have ha : a % n < n := Nat.mod_lt a hn
  exact g ha

/-! ### R3. `interval_cases e` · goal list: one goal per value of `e`; context: `e` replaced everywhere
Needs an upper bound `e < k` in the context (R2); for `ℕ` the lower bound `0` is automatic.
`e` may be a compound term such as `a % 3`: every occurrence, in the goal and in hypotheses, is
replaced by the numeral, and the bound becomes e.g. `hr : 1 < 3`. -/
example (a : ℕ) (P Q : ℕ → Prop) (hr : a % 3 < 3) (hq : Q (a % 3))
    (g : ∀ k, Q k → P k) : P (a % 3) := by
  interval_cases a % 3
  all_goals exact g _ hq

/-! ### R4. `simp_all` · closes the goal, using (and simplifying) every hypothesis
After R3 the goals are closed arithmetic: `h : 2 * 3 % 4 = 1` evaluates to `False`, so the goal
holds vacuously; or the goal evaluates to `True`. -/
example (G : Prop) (h : 2 * 3 % 5 = 4) : G := by
  simp_all

example : 2 = 3 ∨ 3 = 3 := by
  simp_all

/-! ## Part 2 · Euclid's argument -/

/-! ### R5. `Nat.factorial_pos` · context gains `hf : 0 < n.factorial`
`n.factorial` is `n!`. `have hf := e` (no type written) takes the type of `e`. -/
example (n : ℕ) (G : Prop) (g : 0 < n.factorial → G) : G := by
  have hf := Nat.factorial_pos n
  exact g hf

/-! ### R6. `omega` · closes linear arithmetic over `ℕ`/`ℤ` from the hypotheses
It knows truncated subtraction and `%`/`/` by numerals, and treats any other term (here
`n.factorial`) as an unknown. Without `hf` in the context the first goal is false (`0 - 1 = 0`). -/
example (n : ℕ) (hf : 0 < n.factorial) : (6 * n.factorial - 1) % 6 = 5 := by
  omega

example (n : ℕ) (hf : 0 < n.factorial) : 6 * n.factorial - (6 * n.factorial - 1) = 1 := by
  omega

/-! ### R7. `obtain ⟨p, hA, hB, hC⟩ := e` · context: `e : ∃ p, A p ∧ B p ∧ C p` → `p` and three facts
`e` may be a lemma applied to its arguments, e.g. `lemma m (by omega)`. -/
example {α : Type} (A B C : α → Prop) (G : Prop) (e : ∃ p, A p ∧ B p ∧ C p)
    (g : ∀ p, A p → B p → C p → G) : G := by
  obtain ⟨p, hA, hB, hC⟩ := e
  exact g p hA hB hC

/-! ### R8. `refine ⟨p, ?_, hB, hC⟩` · goal: `∃ x, A x ∧ B x ∧ C x` → only the `?_` part, `A p` -/
example {α : Type} (A B C : α → Prop) (p : α) (hA : A p) (hB : B p) (hC : C p) :
    ∃ x, A x ∧ B x ∧ C x := by
  refine ⟨p, ?_, hB, hC⟩
  exact hA

/-! ### R9. `by_contra hle` · goal `G` → `False`; context gains `hle : ¬G` -/
example (n p : ℕ) (g : ¬n < p → False) : n < p := by
  by_contra hle
  exact g hle

/-! ### R10. `push Not at hle` · context: pushes `¬` inward; `¬n < p` becomes `p ≤ n` -/
example (n p : ℕ) (G : Prop) (hle : ¬n < p) (g : p ≤ n → G) : G := by
  push Not at hle
  exact g hle

/-! ### R11. `Nat.Prime.pos`, used as `hp.pos` · context gains `0 < p`
`p.Prime` is `Nat.Prime p`. Dot notation: `hp.pos` is `Nat.Prime.pos hp` because `hp : Nat.Prime p`. -/
example (p : ℕ) (hp : p.Prime) (G : Prop) (g : 0 < p → G) : G := by
  have h0 : 0 < p := hp.pos
  exact g h0

/-! ### R12. `Nat.dvd_factorial` · `0 < m → m ≤ n → m ∣ n.factorial` · context gains `m ∣ n.factorial`
`m ∣ n` (typed `\mid`) is "m divides n". -/
example (m n : ℕ) (hm : 0 < m) (hle : m ≤ n) (G : Prop) (g : m ∣ n.factorial → G) : G := by
  have hd : m ∣ n.factorial := Nat.dvd_factorial hm hle
  exact g hd

/-! ### R13. `dvd_mul_of_dvd_right` · `a ∣ b → ∀ c, a ∣ c * b` · context gains `a ∣ c * b` -/
example {α : Type} [CommMonoid α] (a b c : α) (hab : a ∣ b) (G : Prop) (g : a ∣ c * b → G) : G := by
  have hd : a ∣ c * b := dvd_mul_of_dvd_right hab c
  exact g hd

/-! ### R14. `Nat.dvd_sub` · `k ∣ m → k ∣ n → k ∣ m - n` · context gains `k ∣ m - n`
`have h2 := Nat.dvd_sub h₁ h₂` (no type) shows the subtraction exactly as Lean builds it. -/
example (k m n : ℕ) (hm : k ∣ m) (hn : k ∣ n) (G : Prop) (g : k ∣ m - n → G) : G := by
  have h2 := Nat.dvd_sub hm hn
  exact g h2

/-! ### R15. `rw [show a = b by omega] at h` · context: `h` about `a` → about `b`
`show a = b by tac` is a proof term of `a = b`, built on the spot. -/
example (k x : ℕ) (hx : 0 < x) (h : k ∣ 2 * x - (2 * x - 1)) (G : Prop) (g : k ∣ 1 → G) : G := by
  rw [show 2 * x - (2 * x - 1) = 1 by omega] at h
  exact g h

/-! ### R16. `Nat.dvd_one` · `n ∣ 1 ↔ n = 1`; `.mp` is the `→` direction · context gains `n = 1` -/
example (k : ℕ) (h : k ∣ 1) (G : Prop) (g : k = 1 → G) : G := by
  have h1 : k = 1 := Nat.dvd_one.mp h
  exact g h1

/-! ### R17. `Nat.Prime.one_lt`, used as `hp.one_lt` · context gains `1 < p` -/
example (p : ℕ) (hp : p.Prime) (G : Prop) (g : 1 < p → G) : G := by
  have hlt : 1 < p := hp.one_lt
  exact g hlt

/-! ### R18. `LT.lt.ne'`, used as `hlt.ne'` · `b < a → a ≠ b` · then `a ≠ b` applied to `a = b` is `False`
`a ≠ b` is by definition `a = b → False`, so `hlt.ne' h1 : False` closes a `False` goal. -/
example (p : ℕ) (hlt : 1 < p) (h1 : p = 1) : False := by
  exact hlt.ne' h1

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A residue check mod 3: R1, R2, R3, R4 -/
example (a b : ℕ) (h : a * b % 3 = 2) : a % 3 = 2 ∨ b % 3 = 2 := by
  rw [Nat.mul_mod] at h
  have ha : a % 3 < 3 := Nat.mod_lt a (by norm_num)
  have hb : b % 3 < 3 := Nat.mod_lt b (by norm_num)
  interval_cases a % 3 <;> interval_cases b % 3 <;> simp_all

/-! ### W2. Euclid with `n.factorial + 1`: R5–R12, R14–R18
`Nat.exists_prime_and_dvd : n ≠ 1 → ∃ p, Nat.Prime p ∧ p ∣ n` plays the role that the given lemma
plays in the exercise. -/
example (n : ℕ) : ∃ p, n < p ∧ p.Prime := by
  have hf := Nat.factorial_pos n
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show n.factorial + 1 ≠ 1 by omega)
  refine ⟨p, ?_, hp⟩
  by_contra hle
  push Not at hle
  have h1 : p ∣ n.factorial := Nat.dvd_factorial hp.pos hle
  have h2 := Nat.dvd_sub hpd h1
  rw [show n.factorial + 1 - n.factorial = 1 by omega] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

end M065Guide

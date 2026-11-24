/- Guide for E043 (Primes by norm_num).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `G` stand for "the rest of your goal". A hypothesis `g` in an entry is only there to finish the
example; it shows what the goal or context became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `have`, `exact`, `rcases`, `omega`, dot notation.
-/
import Mathlib

namespace E043Guide

/-! # Part R · Reference entries -/

/-! ## Concrete numbers: `norm_num` decides primality -/

/-! ### R1. `norm_num` on `Nat.Prime n` · closes the goal
Mathlib's `norm_num` has a primality extension: for a numeral `n` it checks that no `d` with
`2 ≤ d`, `d * d ≤ n` divides `n`, and builds the proof. -/
example : Nat.Prime 13 := by
  norm_num

/-! ### R2. `norm_num` on `¬ Nat.Prime n` · closes the goal
For a composite numeral it finds a factor (`21 = 3 * 7`) and proves `n` is not prime. -/
example : ¬ Nat.Prime 21 := by
  norm_num

/-! ## Symbolic primes: lemmas called by dot notation on `hq : Nat.Prime q`
`hq.two_le` is `Nat.Prime.two_le hq`: Lean reads the type of `hq` (`Nat.Prime q`), looks for
`two_le` in the namespace `Nat.Prime`, and passes `hq` as its first explicit argument. -/

/-! ### R3. `Nat.Prime.two_le` · `Nat.Prime p → 2 ≤ p` · context gains `h : 2 ≤ q` -/
example (q : ℕ) (hq : Nat.Prime q) (P : Prop) (g : 2 ≤ q → P) : P := by
  have h := hq.two_le
  exact g h

/-! ### R4. `Nat.Prime.odd_of_ne_two` · `Nat.Prime p → p ≠ 2 → Odd p` · context gains `h : Odd q`
The second argument is the proof of `q ≠ 2`. `Odd q` means `∃ m, q = 2 * m + 1`. -/
example (q : ℕ) (hq : Nat.Prime q) (hne : q ≠ 2) (P : Prop) (g : Odd q → P) : P := by
  have h := hq.odd_of_ne_two hne
  exact g h

/-! ### R5. `Nat.Prime.eq_one_or_self_of_dvd` · `Nat.Prime p → ∀ m, m ∣ p → m = 1 ∨ m = p`
Context gains `h : a = 1 ∨ a = q`: the only divisors of a prime are `1` and itself. Arguments: the
divisor `a` (explicit), then the proof of `a ∣ q`. -/
example (q a : ℕ) (hq : Nat.Prime q) (ha : a ∣ q) (P : Prop) (g : a = 1 ∨ a = q → P) : P := by
  have h := hq.eq_one_or_self_of_dvd a ha
  exact g h

/-! ## Using the disjunction -/

/-! ### R6. `rcases h with h1 | h1` · goal list: one goal per side of `h : A ∨ B`
Both goals are the old goal `G`; the first has `h1 : A`, the second `h1 : B`. `h` is gone.
You can also apply it directly to a lemma: `rcases hq.eq_one_or_self_of_dvd a ha with h1 | h1`. -/
example (A B G : Prop) (h : A ∨ B) (ga : A → G) (gb : B → G) : G := by
  rcases h with h1 | h1
  exacts [ga h1, gb h1]

/-! ### R7. `omega` · closes a linear `ℕ`/`ℤ` goal using the hypotheses
It also closes any goal when a hypothesis is a false numeral equation (`5 = 1`), and it reads
`5 = n` and `n = 5` as the same fact. -/
example (n : ℕ) (h : 5 = 1) : n = 5 := by
  omega

example (n : ℕ) (h : 5 = n) : n = 5 := by
  omega

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R3, then R7: a prime is neither `0` nor `1` -/
example (q : ℕ) (hq : Nat.Prime q) : q ≠ 0 ∧ q ≠ 1 := by
  have h := hq.two_le
  omega

/-! ### W2. R1 inside a term, then R5: the divisors of the concrete prime `7`
`(by norm_num : Nat.Prime 7)` is a proof of `Nat.Prime 7`, and dot notation works on it too. -/
example (a : ℕ) (ha : a ∣ 7) : a = 1 ∨ a = 7 := by
  exact (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd a ha

end E043Guide

/- E43 | Primes by norm_num | 2 min | Nat.Prime, norm_num, mathlib
GOAL
  Decide primality of concrete numbers and use basic facts about primes.

REFERENCE
  example : Nat.Prime 13 := by norm_num        -- norm_num has a primality extension
  example : ¬ Nat.Prime 15 := by norm_num
  #check Nat.Prime.two_le        -- p.Prime → 2 ≤ p
  #check Nat.Prime.odd_of_ne_two -- p.Prime → p ≠ 2 → Odd p
  #check Nat.Prime.eq_one_or_self_of_dvd   -- p.Prime → ∀ a, a ∣ p → a = 1 ∨ a = p
  `hp.two_le` is dot notation for `Nat.Prime.two_le hp` when `hp : p.Prime`.
-/
import Mathlib

-- BEGIN SPEC
theorem prime_97 : Nat.Prime 97 :=
-- END SPEC
  by norm_num

-- BEGIN SPEC
theorem not_prime_91 : ¬ Nat.Prime 91 :=
-- END SPEC
  by norm_num

-- BEGIN SPEC
theorem prime_ge_two (p : ℕ) (hp : p.Prime) : 2 ≤ p :=
-- END SPEC
  hp.two_le

-- BEGIN SPEC
theorem prime_odd (p : ℕ) (hp : p.Prime) (h : p ≠ 2) : Odd p :=
-- END SPEC
  hp.odd_of_ne_two h

-- BEGIN SPEC
theorem three_dvd_prime (p : ℕ) (hp : p.Prime) (h : 3 ∣ p) : p = 3 :=
-- END SPEC
  by
    rcases hp.eq_one_or_self_of_dvd 3 h with h3 | h3
    · omega
    · omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Concrete numbers: `norm_num`. Symbolic primes: a library lemma via dot notation on `hp`.
H2. `three_dvd_prime`: a divisor of a prime is 1 or the prime itself.
H3. `rcases hp.eq_one_or_self_of_dvd 3 h with h3 | h3` then `omega` in both cases.
-/

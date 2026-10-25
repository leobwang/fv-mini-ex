/- H07 | Infinitely many primes | 45-60 min | strong induction, Nat.Prime, factorial, mathlib
GOAL
  Prove from scratch that above every `n` there is a prime: first that every `n ≥ 2` has a prime
  factor (strong induction), then Euclid's argument with `n! + 1`.

REFERENCE
  #check Nat.prime_def      -- p.Prime ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
  #check Nat.dvd_factorial  -- 0 < m → m ≤ n → m ∣ n !
  #check Nat.dvd_add_right  -- k ∣ m → (k ∣ m + n ↔ k ∣ n)
  #check Nat.le_of_dvd      -- 0 < n → m ∣ n → m ≤ n
  example (n : ℕ) (P : ℕ → Prop) (h : ∀ n, (∀ m < n, P m) → P n) : P n := Nat.strong_induction_on n h
  -- `induction n using Nat.strong_induction_on with | _ n ih => ...`;  `push Not at hp` on `¬ (... ∧ ∀ ...)`
BANNED: Nat.exists_infinite_primes, Nat.minFac, Nat.minFac_prime, Nat.minFac_dvd, Nat.exists_prime_and_dvd, Nat.infinite_setOf_prime, Nat.primeFactors, Nat.primeFactorsList, Nat.not_bddAbove_setOf_prime
-/
import Mathlib

namespace H07

-- MILESTONE (optional: change or delete)
theorem exists_prime_dvd (n : ℕ) (hn : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n := by
  sorry

-- BEGIN SPEC
theorem infinitely_many_primes (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
-- END SPEC
  sorry

end H07

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Take a prime factor `p` of `n! + 1`. If `p < n`, then `p` divides both `n!` and `n! + 1`.
H2. Prime factor by strong induction: if `n` is not prime, `Nat.prime_def` gives a divisor `m` with `m ≠ 1`, `m ≠ n`, hence `2 ≤ m < n`; apply the IH to `m`.
H3. Main: `obtain ⟨p, hp, hpd⟩ := exists_prime_dvd (n.factorial + 1) _`, then `by_contra`, `Nat.dvd_factorial hp.pos hlt.le`, `(Nat.dvd_add_right h1).mp hpd : p ∣ 1`.
-/

/- M43 | Primes and products | 10 min | Nat.Prime, Euclid's lemma, divisibility, mathlib
GOAL
  Use Euclid's lemma (`p ∣ m * n → p ∣ m ∨ p ∣ n`) to reason about prime divisors of products
  and squares.

REFERENCE
  #check Nat.Prime.dvd_mul   -- p.Prime → (p ∣ m * n ↔ p ∣ m ∨ p ∣ n)
  #check pow_two             -- a ^ 2 = a * a
  #check mul_dvd_mul         -- a ∣ b → c ∣ d → a * c ∣ b * d
  example (p a b : ℕ) (hp : p.Prime) (h : p ∣ a * b) (hb : ¬ p ∣ b) : p ∣ a := by
    rcases hp.dvd_mul.mp h with h | h
    · exact h
    · exact absurd h hb
BANNED: Nat.Prime.dvd_of_dvd_pow, Prime.dvd_of_dvd_pow, Nat.Prime.dvd_mul_of_dvd_left
-/
import Mathlib

namespace M43

-- BEGIN SPEC
theorem prime_dvd_sq (p a : ℕ) (hp : p.Prime) (h : p ∣ a ^ 2) : p ∣ a :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem prime_sq_dvd_sq (p a : ℕ) (hp : p.Prime) (h : p ∣ a ^ 2) : p ^ 2 ∣ a ^ 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem prime_dvd_three (p a b c : ℕ) (hp : p.Prime) (h : p ∣ a * b * c) :
    p ∣ a ∨ p ∣ b ∨ p ∣ c :=
-- END SPEC
  sorry

end M43

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write squares as products (`pow_two`) and apply `hp.dvd_mul`.
H2. `a * b * c` parses as `(a * b) * c`: apply Euclid's lemma twice.
H3. `rw [pow_two] at h; rcases hp.dvd_mul.mp h with h | h <;> exact h`; then `mul_dvd_mul ha ha` for the squared version.
-/

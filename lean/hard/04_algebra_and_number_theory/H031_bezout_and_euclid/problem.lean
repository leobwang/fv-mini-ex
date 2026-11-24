/- H031 | Bézout and Euclid's lemma | 45-75 min | gcd induction, Int casts, exact_mod_cast, mathlib
GOAL
  Prove Bézout's identity `x * a + y * b = gcd a b` (integers `x, y`) by following Euclid's
  algorithm, then use it for Euclid's lemma: a prime `p` with `p ∣ a * b` divides `a` or `b`.

REFERENCE
  -- `induction a, b using Nat.gcd.induction with | H0 n => _ | H1 m n hm ih => _`  (P 0 n; 0 < m → P (n % m) m → P m n)
  #check Nat.gcd_rec        -- gcd m n = gcd (n % m) m
  #check Nat.mod_add_div    -- m % k + k * (m / k) = m
  #check Nat.Prime.eq_one_or_self_of_dvd  -- p.Prime → ∀ m, m ∣ p → m = 1 ∨ m = p
  #check Nat.gcd_dvd_left   -- gcd m n ∣ m   (and `Nat.gcd_dvd_right`: gcd m n ∣ n)
  #check Int.natCast_dvd_natCast  -- (↑m : ℤ) ∣ ↑n ↔ m ∣ n
  example (m n : ℕ) (h : m % n + n * (m / n) = m) : ((m % n : ℕ) : ℤ) + n * (m / n : ℕ) = m := by exact_mod_cast h
  -- `(k : ℤ)` / `↑k` is the cast ℕ → ℤ; `exact_mod_cast` / `push_cast` move casts through `+`, `*`.
  -- `a ∣ b` (typed `\mid`) is "a divides b": `∃ c, b = a * c`, so `⟨c, h⟩` builds one.
BANNED: exact?, apply?, rw?, hint, try?
BANNED: Nat.gcd_eq_gcd_ab, Int.gcd_eq_gcd_ab, Nat.xgcd, Nat.xgcd_val, Nat.xgcdAux, Nat.gcdA, Nat.gcdB, Int.gcd_dvd_iff, Int.gcd_least_linear, Nat.exists_mul_mod_eq_gcd, exists_gcd_eq_mul_add_mul, gcd_dvd_iff_exists, Finset.gcd_eq_sum_mul, IsBezout, Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le, Ideal, Ideal.mem_span_pair, IsCoprime
BANNED: Nat.Prime.dvd_mul, Int.Prime.dvd_mul', Nat.Prime.dvd_or_dvd, Nat.Prime.not_dvd_mul, Nat.Prime.prime, Nat.prime_iff, irreducible_iff_prime, Nat.prime_iff_prime_int, Int.prime_iff_natAbs_prime, exists_dvd_and_dvd_of_dvd_mul, IsPrimal, DecompositionMonoid.primal, gcd_mul_dvd_mul_gcd, Nat.divisors_mul
BANNED: Nat.primeFactors, Nat.mem_primeFactors, Nat.primeFactors_mul, Nat.primeFactorsList, Nat.mem_primeFactorsList, Nat.mem_primeFactorsList_mul, Nat.perm_primeFactorsList_mul, Nat.factorization, Nat.factorization_mul, Nat.Prime.factorization_pos_of_dvd, Nat.Prime.dvd_iff_one_le_factorization, Nat.Prime.emultiplicity_mul, padicValNat, ZMod, Fact
BANNED: Nat.Coprime, Nat.Coprime.dvd_mul_left, Nat.Coprime.dvd_mul_right, Nat.Coprime.dvd_of_dvd_mul_left, Nat.Coprime.dvd_of_dvd_mul_right, Nat.Coprime.gcd_mul, Nat.Coprime.gcd_mul_left_cancel, Nat.Coprime.gcd_mul_right_cancel, Nat.Coprime.gcd_mul_left_cancel_right, Nat.Coprime.gcd_mul_right_cancel_right, Int.dvd_of_dvd_mul_left_of_gcd_one, Int.dvd_of_dvd_mul_right_of_gcd_one, Nat.gcd_mul_left_left_of_gcd_eq_one, Nat.gcd_mul_left_right_of_gcd_eq_one, Nat.gcd_mul_right_left_of_gcd_eq_one, Nat.gcd_mul_right_right_of_gcd_eq_one, Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime, Nat.dvd_gcd_mul_iff_dvd_mul, Nat.dvd_mul_gcd_iff_dvd_mul, Nat.dvd_gcd_mul_gcd_iff_dvd_mul, Nat.gcd_mul_left_dvd_mul_gcd, Nat.gcd_mul_right_dvd_mul_gcd, Nat.isCoprime_iff_coprime, Int.isCoprime_iff_gcd_eq_one, Nat.Coprime.isCoprime, Nat.coprime_iff_gcd_eq_one, Nat.coprime_or_dvd_of_prime, Nat.Prime.coprime_iff_not_dvd, Nat.Prime.dvd_iff_not_coprime, Nat.Prime.not_coprime_iff_dvd, Nat.coprime_primes, Nat.coprime_comm, Nat.coprime_of_lt_prime, Nat.Prime.coprime_pow_of_not_dvd
NOTE: library Bézout/Euclid, `Nat.Coprime` and its lemmas (so also `dvd_mul_left`/`dvd_mul_right`), factorizations and `ZMod` are banned; you need none of them. Build `a ∣ b` as `⟨c, h⟩` or `Dvd.intro c (h : a * c = b)`.
-/
import Mathlib

namespace H031

-- MILESTONE (optional: change or delete)
theorem gcd_step (m n : ℕ) (x y : ℤ) (h : x * (n % m : ℕ) + y * m = Nat.gcd (n % m) m) :
    (y - x * (n / m : ℕ)) * m + x * n = Nat.gcd m n := by
  sorry

-- BEGIN SPEC
theorem bezout (a b : ℕ) : ∃ x y : ℤ, x * a + y * b = Nat.gcd a b :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
theorem gcd_eq_one_of_not_dvd (p a : ℕ) (hp : p.Prime) (ha : ¬ p ∣ a) : Nat.gcd p a = 1 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem int_dvd_of_bezout (p a b : ℕ) (x y : ℤ) (hxy : x * p + y * a = 1) (h : (p : ℤ) ∣ a * b) :
    (p : ℤ) ∣ b := by
  sorry

-- BEGIN SPEC
theorem euclid (p a b : ℕ) (hp : p.Prime) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
-- END SPEC
  sorry

end H031

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Euclid's algorithm replaces `(m, n)` by `(n % m, m)` without changing the gcd: carry the
    coefficients along. For Euclid's lemma, if `p ∤ a` then `gcd p a` is `1` (it divides the prime `p`).
H2. Bézout: `Nat.gcd.induction`. Base: `gcd 0 n = n`, so take `(0, 1)`. Step: from
    `x * (n % m) + y * m = gcd` and `n % m = n - m * (n / m)` (in ℤ) read off new coefficients.
    Euclid: Bézout for `(p, a)` gives `x * p + y * a = 1`; multiply by `b` and use `a * b = p * c`.
H3. Step: `refine ⟨y - x * (n / m : ℕ), x, ?_⟩`, `rw [Nat.gcd_rec m n, ← h]`, then
    `have h' : ((n % m : ℕ) : ℤ) = n - m * (n / m : ℕ)` (from `Nat.mod_add_div` by `exact_mod_cast`), `rw [h']; ring`.
    Euclid: `(b : ℤ) = (x * p + y * a) * b = p * (x * b + y * c)`, then `Int.natCast_dvd_natCast.mp ⟨_, this⟩`.
-/

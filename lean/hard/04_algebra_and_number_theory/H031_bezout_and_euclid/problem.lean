/- H031 | Bézout and Euclid's lemma | 45-75 min | gcd induction, Int casts, exact_mod_cast, mathlib
GOAL
  Prove Bézout's identity `x * a + y * b = gcd a b` (integers `x, y`) by following Euclid's
  algorithm, then use it for Euclid's lemma: a prime `p` with `p ∣ a * b` divides `a` or `b`.

BANNED: exact?, apply?, rw?, hint, try?
BANNED: Nat.gcd_eq_gcd_ab, Int.gcd_eq_gcd_ab, Nat.xgcd, Nat.xgcd_val, Nat.xgcdAux, Nat.gcdA, Nat.gcdB, Int.gcd_dvd_iff, Int.gcd_least_linear, Nat.exists_mul_mod_eq_gcd, exists_gcd_eq_mul_add_mul, gcd_dvd_iff_exists, Finset.gcd_eq_sum_mul, IsBezout, Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le, Ideal, Ideal.mem_span_pair, IsCoprime
BANNED: Nat.Prime.dvd_mul, Int.Prime.dvd_mul', Nat.Prime.dvd_or_dvd, Nat.Prime.not_dvd_mul, Nat.Prime.prime, Nat.prime_iff, irreducible_iff_prime, Nat.prime_iff_prime_int, Int.prime_iff_natAbs_prime, exists_dvd_and_dvd_of_dvd_mul, IsPrimal, DecompositionMonoid.primal, gcd_mul_dvd_mul_gcd, Nat.divisors_mul
BANNED: Nat.primeFactors, Nat.mem_primeFactors, Nat.primeFactors_mul, Nat.primeFactorsList, Nat.mem_primeFactorsList, Nat.mem_primeFactorsList_mul, Nat.perm_primeFactorsList_mul, Nat.factorization, Nat.factorization_mul, Nat.Prime.factorization_pos_of_dvd, Nat.Prime.dvd_iff_one_le_factorization, Nat.Prime.emultiplicity_mul, padicValNat, ZMod, Fact
BANNED: Nat.Coprime, Nat.Coprime.dvd_mul_left, Nat.Coprime.dvd_mul_right, Nat.Coprime.dvd_of_dvd_mul_left, Nat.Coprime.dvd_of_dvd_mul_right, Nat.Coprime.gcd_mul, Nat.Coprime.gcd_mul_left_cancel, Nat.Coprime.gcd_mul_right_cancel, Nat.Coprime.gcd_mul_left_cancel_right, Nat.Coprime.gcd_mul_right_cancel_right, Int.dvd_of_dvd_mul_left_of_gcd_one, Int.dvd_of_dvd_mul_right_of_gcd_one, Nat.gcd_mul_left_left_of_gcd_eq_one, Nat.gcd_mul_left_right_of_gcd_eq_one, Nat.gcd_mul_right_left_of_gcd_eq_one, Nat.gcd_mul_right_right_of_gcd_eq_one, Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime, Nat.dvd_gcd_mul_iff_dvd_mul, Nat.dvd_mul_gcd_iff_dvd_mul, Nat.dvd_gcd_mul_gcd_iff_dvd_mul, Nat.gcd_mul_left_dvd_mul_gcd, Nat.gcd_mul_right_dvd_mul_gcd, Nat.isCoprime_iff_coprime, Int.isCoprime_iff_gcd_eq_one, Nat.Coprime.isCoprime, Nat.coprime_iff_gcd_eq_one, Nat.coprime_or_dvd_of_prime, Nat.Prime.coprime_iff_not_dvd, Nat.Prime.dvd_iff_not_coprime, Nat.Prime.not_coprime_iff_dvd, Nat.coprime_primes, Nat.coprime_comm, Nat.coprime_of_lt_prime, Nat.Prime.coprime_pow_of_not_dvd

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H031

/- SKELETON · gcd_step   (milestone; prove it FIRST; it is the whole H1 case of bezout)
  1. Right side: one Euclid step on the gcd, then replace `↑((n % m).gcd m)`
     by the left side of `h`:                                                         R1, rw [← h]
  2. `%` is not a ring operation, so restate it in ℤ first:
       h' : ((n % m : ℕ) : ℤ) = n - m * (n / m : ℕ)
     proof: subtraction → addition, then the ℕ division identity through the casts:   R2, R3 → R4
  3. Substitute `h'`; what is left is ring algebra with `↑(n / m)` as an unknown:      rw [h'], R5
-/
-- MILESTONE (optional: change or delete)
theorem gcd_step (m n : ℕ) (x y : ℤ) (h : x * (n % m : ℕ) + y * m = Nat.gcd (n % m) m) :
    (y - x * (n / m : ℕ)) * m + x * n = Nat.gcd m n := by
  sorry

/- SKELETON · bezout
  0. Prove the milestone gcd_step first (used in step 3).
  1. Induct on the pair along Euclid's algorithm, naming the cases H0 n, H1 m n hm ih:  R6
  2. H0 (`gcd 0 n = n`): witnesses `0, 1`; the arithmetic is `simp`:                   R7, R9 (uses R8)
  3. H1: unpack `ih` into `x y h`:                                                     R10
     witnesses `y - x * (n / m : ℕ)` and `x`; the equation is `gcd_step m n x y h`:     R7
-/
-- BEGIN SPEC
theorem bezout (a b : ℕ) : ∃ x y : ℤ, x * a + y * b = Nat.gcd a b :=
-- END SPEC
  sorry

/- SKELETON · gcd_eq_one_of_not_dvd   (milestone; euclid uses it to make the Bézout sum 1)
  1. `gcd p a ∣ p`, so `gcd p a` is 1 or p; split the two cases:                       R11, R12, R13
  2. gcd p a = 1: that is the goal.                                                    exact
  3. gcd p a = p: transport `gcd p a ∣ a` along it to `p ∣ a`, contradicting `ha`:      R11, R14, R15
-/
-- MILESTONE (optional: change or delete)
theorem gcd_eq_one_of_not_dvd (p a : ℕ) (hp : p.Prime) (ha : ¬ p ∣ a) : Nat.gcd p a = 1 := by
  sorry

/- SKELETON · int_dvd_of_bezout   (milestone; Euclid's lemma in ℤ once gcd p a = 1)
  1. Unpack `h` into the quotient `c` and `hc : ↑a * ↑b = ↑p * c`:                       R16
  2. Choose the quotient `x * ↑b + y * c`; the goal becomes `↑b = ↑p * (x * ↑b + y * c)`: R17
  3. Chain of equations:                                                               R18
       ↑b = (x * ↑p + y * ↑a) * ↑b           rw [hxy] then R19
          = x * ↑p * ↑b + y * (↑a * ↑b)      R5
          = ↑p * (x * ↑b + y * c)            rw [hc] then R5
-/
-- MILESTONE (optional: change or delete)
theorem int_dvd_of_bezout (p a b : ℕ) (x y : ℤ) (hxy : x * p + y * a = 1) (h : (p : ℤ) ∣ a * b) :
    (p : ℤ) ∣ b := by
  sorry

/- SKELETON · euclid
  0. Uses bezout and the milestones gcd_eq_one_of_not_dvd (step 3), int_dvd_of_bezout (step 5).
  1. Case on `p ∣ a`; if it holds, take the left disjunct:                             R20, R21
  2. Otherwise go right, and take Bézout for `(p, a)`: obtain `x y hxy`:                R21, R10
  3. In `hxy`, rewrite the gcd to 1 (milestone) and `↑1` to `1`:
       hxy : x * ↑p + y * ↑a = 1                                                       R22
  4. Lift `h` to ℤ:   h' : (p : ℤ) ∣ a * b                                              R4
  5. int_dvd_of_bezout gives `↑p ∣ ↑b`; bring it back to ℕ:                             R23
-/
-- BEGIN SPEC
theorem euclid (p a b : ℕ) (hp : p.Prime) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
-- END SPEC
  sorry

end H031

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Euclid's algorithm replaces `(m, n)` by `(n % m, m)` without changing the gcd (R1): carry the
    Bézout coefficients along it with `Nat.gcd.induction` (R6). For Euclid's lemma, if `p ∤ a` then
    `gcd p a = 1`, since it divides the prime `p` (R11, R12); Bézout then gives `x * p + y * a = 1`.
H2. gcd_step: `rw [Nat.gcd_rec m n, ← h]`, restate `↑(n % m)` in ℤ, `rw` it, `ring`. bezout: case H0
    takes `(0, 1)` and `simp`; case H1 unpacks `ih` and applies gcd_step. euclid: `by_cases ha : p ∣ a`;
    otherwise multiply `x * p + y * a = 1` by `b` and use `a * b = p * c`, all in ℤ (int_dvd_of_bezout),
    then come back to ℕ with `Int.natCast_dvd_natCast.mp`.
H3. `have h' : ((n % m : ℕ) : ℤ) = n - m * (n / m : ℕ) := by rw [eq_sub_iff_add_eq]; exact_mod_cast Nat.mod_add_div n m`.
    In the `H1` case: `exact ⟨y - x * (n / m : ℕ), x, gcd_step m n x y h⟩`. Milestone 2:
    `rcases hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left p a) with h1 | h1`, the second case by
    `absurd (h1 ▸ Nat.gcd_dvd_right p a) ha`. Milestone 3: `refine ⟨x * b + y * c, ?_⟩` and
    `calc (b : ℤ) = (x * p + y * a) * b := by rw [hxy, one_mul]` `_ = x * p * b + y * (a * b) := by ring` `_ = …`.
-/

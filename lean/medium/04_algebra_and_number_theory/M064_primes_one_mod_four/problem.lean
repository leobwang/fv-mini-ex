/- M064 | Infinitely many primes ≡ 1 mod 4 | 15-20 min | ZMod, casts, Fact, Nat.Prime, mathlib
GOAL
  Above every `n` there is a prime `p` with `p % 4 = 1`. Take a prime factor `p` of `(2 * n.factorial)^2 + 1`
  (`n.factorial` is n!). Then `-1` is a square in `ZMod p` (so `p % 4 ≠ 3`, a library fact), `p` is odd,
  and `p > n`.

REFERENCE
  #check Nat.exists_prime_and_dvd  -- n ≠ 1 → ∃ p, p.Prime ∧ p ∣ n
  #check ZMod.natCast_eq_zero_iff  -- (a b : ℕ) : ((a : ZMod b) = 0 ↔ b ∣ a)
  #check ZMod.mod_four_ne_three_of_sq_eq_neg_one  -- [Fact p.Prime] → y ^ 2 = -1 → p % 4 ≠ 3
  example (p : ℕ) (hp : p.Prime) : Fact p.Prime := ⟨hp⟩  -- inside a proof: `haveI := Fact.mk hp`
  #check eq_neg_iff_add_eq_zero    -- a = -b ↔ a + b = 0
  example (a p : ℕ) (h : ((a ^ 2 + 1 : ℕ) : ZMod p) = 0) : (a : ZMod p) ^ 2 + 1 = 0 := by exact_mod_cast h
  #check Nat.dvd_factorial         -- 0 < m → m ≤ n → m ∣ n.factorial
  #check Nat.dvd_add_right         -- k ∣ m → (k ∣ m + n ↔ k ∣ n)
  #check Nat.Prime.eq_two_or_odd   -- p = 2 ∨ p % 2 = 1
NOTE: `ZMod p` is the ring ℤ/pℤ and `(k : ZMod p)` is `k` mod `p`; `Fact P` packages a proof of `P` as an instance.
BANNED: Nat.forall_exists_prime_gt_and_modEq, Nat.forall_exists_prime_gt_and_eq_mod, Nat.forall_exists_prime_gt_and_zmodEq
BANNED: Nat.infinite_setOf_prime_and_modEq, Nat.infinite_setOf_prime_and_eq_mod, Nat.frequently_atTop_prime_and_modEq
BANNED: Nat.exists_prime_gt_modEq_one, Nat.infinite_setOf_prime_modEq_one, Nat.frequently_atTop_modEq_one, Filter, Frequently
-/
import Mathlib

namespace M064

-- BEGIN SPEC
theorem primes_one_mod_four (n : ℕ) : ∃ p, n < p ∧ p.Prime ∧ p % 4 = 1 :=
-- END SPEC
  sorry

end M064

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three facts about a prime `p ∣ (2 * n.factorial)^2 + 1`: `p % 4 ≠ 3`, `p ≠ 2`, and `¬ p ≤ n`.
    Together with `p % 2 = 1` they force `p % 4 = 1` (`omega`).
H2. Get `p` from `Nat.exists_prime_and_dvd`. For `p % 4 ≠ 3`, show `((2 * n.factorial : ℕ) : ZMod p) ^ 2 = -1`
    from `p ∣ ...` via `ZMod.natCast_eq_zero_iff`. If `p ≤ n` then `p ∣ (2 * n.factorial)^2`, so `p ∣ 1`.
H3. `haveI := Fact.mk hp`;
    `have hsq : ((2 * n.factorial : ℕ) : ZMod p) ^ 2 = -1 := by
       rw [eq_neg_iff_add_eq_zero]; exact_mod_cast (ZMod.natCast_eq_zero_iff _ p).mpr hpd`;
    then `ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq`.
-/

/- H034 | When is −1 a square mod p? | 1-1.5 h | ZMod, Fermat, Wilson, factorial products, mathlib
GOAL
  For a prime `p`, prove `-1` is a square in `ZMod p` (the integers mod `p`) iff `p % 4 ≠ 3`.
  (→) Fermat: if `p = 4k+3` then `1 = x^(p-1) = (x²)^(2k+1) = -1`. (←) Wilson: if `p = 4k+1` then
  `((2k)!)² = -1`, from `(2n)! = (-1)^n (n!)²` in `ZMod (2n+1)`. Mathlib's Fermat and Wilson are allowed.

REFERENCE
  #check ZMod.pow_card_sub_one_eq_one   -- [Fact p.Prime] (ha : a ≠ 0) : a ^ (p - 1) = 1   (Fermat)
  #check ZMod.wilsons_lemma             -- [Fact p.Prime] : (((p - 1)! : ℕ) : ZMod p) = -1  (Wilson)
  #check ZMod.natCast_eq_zero_iff       -- ((a : ℕ) : ZMod b) = 0 ↔ b ∣ a
  #check ZMod.neg_one_ne_one            -- [Fact (2 < n)] : (-1 : ZMod n) ≠ 1
  #check Nat.factorial_mul_ascFactorial -- n ! * (n + 1).ascFactorial k = (n + k)!
  #check Nat.ascFactorial_eq_prod_range -- n.ascFactorial k = ∏ i ∈ range k, (n + i)
  #check Finset.prod_neg                -- ∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x   (#s = s.card)
  #check Finset.prod_range_reflect      -- ∏ j ∈ range n, f (n - 1 - j) = ∏ j ∈ range n, f j
  #check Finset.prod_range_add_one_eq_factorial -- ∏ i ∈ range n, (i + 1) = n !
  example [Fact (Nat.Prime 2)] : ∃ x : ZMod 2, x ^ 2 = -1 := ⟨1, by decide +revert⟩  -- tiny ZMod goal
  -- casts: `Nat.cast_mul`, `Nat.cast_prod`, `push_cast`;  instance by hand: `haveI : Fact (2 < p) := ⟨by omega⟩`
BANNED: ZMod.exists_sq_eq_neg_one_iff, ZMod.mod_four_ne_three_of_sq_eq_neg_one, ZMod.mod_four_ne_three_of_sq_eq_neg_sq, ZMod.mod_four_ne_three_of_sq_eq_neg_sq', Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one, ZMod.euler_criterion, ZMod.euler_criterion_units, FiniteField.isSquare_neg_one_iff, FiniteField.isSquare_iff, FiniteField.unit_isSquare_iff, ZMod.isSquare_neg_one_iff', ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three, ZMod.isSquare_neg_one_of_dvd, ZMod.isSquare_neg_one_mul, ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime, ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime, quadraticChar_neg_one, quadraticChar_neg_one_iff_not_isSquare, quadraticChar_one_iff_isSquare, quadraticChar_exists_neg_one, ZMod.χ₄, legendreSym, legendreSym.at_neg_one, jacobiSym, Nat.Prime.sq_add_sq, Nat.eq_sq_add_sq_iff, Nat.eq_sq_add_sq_iff_eq_sq_mul, Nat.eq_sq_add_sq_of_isSquare_mod_neg_one, GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible, GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime, GaussianInt.mod_four_eq_three_of_nat_prime_of_prime, IsSquare, exact?, apply?, rw?, try?, hint
NOTE: `x ^ 2 = -1` lives in `ZMod p`; `(k : ZMod p)` for `k : ℕ` is a cast, so `p` itself casts to `0`.
-/
import Mathlib

namespace H034

open Finset

-- MILESTONE (optional: change or delete)
theorem half_factorial (n : ℕ) :
    ((2 * n).factorial : ZMod (2 * n + 1)) = (-1) ^ n * (n.factorial : ZMod (2 * n + 1)) ^ 2 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem not_sq_of_three_mod_four (p : ℕ) [Fact p.Prime] (h : p % 4 = 3) (x : ZMod p) :
    x ^ 2 ≠ -1 := by
  sorry

-- BEGIN SPEC
theorem neg_one_sq_iff (p : ℕ) [Fact p.Prime] : (∃ x : ZMod p, x ^ 2 = -1) ↔ p % 4 ≠ 3 :=
-- END SPEC
  sorry

end H034

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (→): `x ≠ 0` (else `0 = -1`), so Fermat gives `x ^ (p - 1) = 1`; with `p - 1 = 2 * (2k + 1)` this is `(x ^ 2) ^ (2k + 1) = (-1) ^ (2k + 1) = -1`. (←): `p = 2` by `⟨1, by decide +revert⟩` (plain `decide` fails: the local `Fact` instance is a free variable); otherwise `p = 2 * (2k) + 1` and the witness is `(2k)!`.
H2. `half_factorial`: `(2n)! = n! * ∏ i ∈ range n, (n + 1 + i)`, and in `ZMod (2n+1)` each factor `n + 1 + i` equals `-(n - i)` because the two add up to `2n + 1`. The `n - i` reassemble into `n!` by `prod_range_reflect`.
H3. `have h2 : ∀ i ∈ range n, ((n + 1 + i : ℕ) : ZMod (2 * n + 1)) = -((n - i : ℕ) : ZMod (2 * n + 1))` via `eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff`; then `rw [h1, Nat.cast_mul, Nat.cast_prod, prod_congr rfl h2, prod_neg, card_range, ← Nat.cast_prod, h3]; ring`. For (←), `subst` `p` and take `hw := ZMod.wilsons_lemma (p := 2 * (2 * k) + 1)`; then `rw [Nat.add_sub_cancel, half_factorial, pow_mul, neg_one_sq, one_pow, one_mul] at hw` (`Nat.add_sub_cancel` first turns `(2 * (2k) + 1 - 1)!` into `(2 * (2k))!`).
-/

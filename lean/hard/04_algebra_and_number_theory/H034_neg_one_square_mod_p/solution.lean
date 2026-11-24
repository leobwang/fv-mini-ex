/- H034 | When is −1 a square mod p? | 1-1.5 h | ZMod, Fermat, Wilson, factorial products, mathlib
GOAL
  For a prime `p`, prove `-1` is a square in `ZMod p` (the integers mod `p`) iff `p % 4 ≠ 3`.
  (→) Fermat: if `p = 4k+3` then `1 = x^(p-1) = (x²)^(2k+1) = -1`. (←) Wilson: if `p = 4k+1` then
  `((2k)!)² = -1`, from `(2n)! = (-1)^n (n!)²` in `ZMod (2n+1)`. Mathlib's Fermat and Wilson are allowed.
BANNED: ZMod.exists_sq_eq_neg_one_iff, ZMod.mod_four_ne_three_of_sq_eq_neg_one, ZMod.mod_four_ne_three_of_sq_eq_neg_sq, ZMod.mod_four_ne_three_of_sq_eq_neg_sq', Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one, ZMod.euler_criterion, ZMod.euler_criterion_units, FiniteField.isSquare_neg_one_iff, FiniteField.isSquare_iff, FiniteField.unit_isSquare_iff, ZMod.isSquare_neg_one_iff', ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three, ZMod.isSquare_neg_one_of_dvd, ZMod.isSquare_neg_one_mul, ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime, ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime, quadraticChar_neg_one, quadraticChar_neg_one_iff_not_isSquare, quadraticChar_one_iff_isSquare, quadraticChar_exists_neg_one, ZMod.χ₄, legendreSym, legendreSym.at_neg_one, jacobiSym, Nat.Prime.sq_add_sq, Nat.eq_sq_add_sq_iff, Nat.eq_sq_add_sq_iff_eq_sq_mul, Nat.eq_sq_add_sq_of_isSquare_mod_neg_one, GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible, GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime, GaussianInt.mod_four_eq_three_of_nat_prime_of_prime, IsSquare, exact?, apply?, rw?, try?, hint

GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H034

open Finset

/- SKELETON · half_factorial  (MILESTONE: prove it FIRST; used in step 3 of neg_one_sq_iff)
  Idea: in ZMod (2n+1), (2n)! = n! · ∏_{i<n} (n+1+i) and n+1+i = -(n-i), so ∏ = (-1)^n · n!.
  1. h1 : (2 * n).factorial = n.factorial * ∏ i ∈ range n, (n + 1 + i)            (in ℕ)
       fold the product, merge with n!, then 2 * n = n + n                          R1 → R2 → R3
  2. h2 : ∀ i ∈ range n, ((n + 1 + i : ℕ) : ZMod (2 * n + 1)) = -((n - i : ℕ) : ZMod (2 * n + 1))
       `intro i hi`, then hi : i < n                                                R4
       a = -b  →  a + b = 0  →  one cast ↑(… + …) = 0  →  2 * n + 1 ∣ …            R5 → R6 → R7
       the sum is 2 * n + 1 (omega, with hi); `rw` then closes the `∣` goal        R8
  3. h3 : ∏ i ∈ range n, (n - i) = n.factorial                                     (in ℕ)
       unfold n! into a product, reverse the LEFT product                           R9 → R10
       compare factor by factor, then `intro i hi`; each factor goal is ℕ arithmetic  R11, R4, omega
  4. Main goal: `rw [h1]`, push the cast through `*` and `∏`                        R12, R13
       negate every factor with h2                                                  R14
       pull the signs out and count them                                            R15, R16
       fold the cast back, `rw [h3]`, close with `ring`                             R13 (←), rw [h3], ring
-/
-- MILESTONE (optional: change or delete)
theorem half_factorial (n : ℕ) :
    ((2 * n).factorial : ZMod (2 * n + 1)) = (-1) ^ n * (n.factorial : ZMod (2 * n + 1)) ^ 2 := by
  have h1 : (2 * n).factorial = n.factorial * ∏ i ∈ range n, (n + 1 + i) := by
    rw [← Nat.ascFactorial_eq_prod_range, Nat.factorial_mul_ascFactorial, two_mul]
  -- WHY: `n + 1 + i` and `n - i` sum to the modulus `2n + 1`, so they are negatives in `ZMod (2n+1)`.
  have h2 : ∀ i ∈ range n,
      ((n + 1 + i : ℕ) : ZMod (2 * n + 1)) = -((n - i : ℕ) : ZMod (2 * n + 1)) := by
    intro i hi
    rw [mem_range] at hi
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff,
      show n + 1 + i + (n - i) = 2 * n + 1 by omega]
  have h3 : ∏ i ∈ range n, (n - i) = n.factorial := by
    rw [← prod_range_add_one_eq_factorial, ← prod_range_reflect]
    exact prod_congr rfl fun i hi => by rw [mem_range] at hi; omega
  rw [h1, Nat.cast_mul, Nat.cast_prod, prod_congr rfl h2, prod_neg, card_range, ← Nat.cast_prod, h3]
  ring

/- SKELETON · not_sq_of_three_mod_four  (MILESTONE: prove it FIRST; used in step 2 of neg_one_sq_iff)
  Idea: p - 1 = 2(2k+1), so Fermat gives 1 = x^(p-1) = (x^2)^(2k+1) = (-1)^(2k+1) = -1.
  1. `intro hx`; the goal is False
  2. hx0 : x ≠ 0: substitute x := 0, then hx simplifies to False                  R17, R18
  3. the instance Fact (2 < p): 2 ≤ p from the prime, then omega with h            R19, R20
  4. Fermat: hfl : x ^ (p - 1) = 1                                                 R21
  5. k with p - 1 = 2 * (2 * k + 1) (witness p / 4)                               R22
  6. in hfl: `rw [hk]`, split the exponent, `rw [hx]`, the odd power of -1;
     hfl becomes -1 = 1                                                           rw [hk], R23, rw [hx], R24
  7. contradiction with -1 ≠ 1 in ZMod p                                          R25
-/
-- MILESTONE (optional: change or delete)
theorem not_sq_of_three_mod_four (p : ℕ) [Fact p.Prime] (h : p % 4 = 3) (x : ZMod p) :
    x ^ 2 ≠ -1 := by
  intro hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  haveI : Fact (2 < p) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  have hfl := ZMod.pow_card_sub_one_eq_one hx0
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 * (2 * k + 1) := ⟨p / 4, by omega⟩
  rw [hk, pow_mul, hx, (odd_two_mul_add_one k).neg_one_pow] at hfl
  exact ZMod.neg_one_ne_one hfl

/- SKELETON · neg_one_sq_iff  (prove half_factorial and not_sq_of_three_mod_four first)
  1. `constructor`: two directions
  2. (→): introduce the witness x, hx and h3 : p % 4 = 3; apply not_sq_of_three_mod_four   R26
  3. (←): `intro h`; split p = 2 | p odd with the prime from the instance                  R19, R27
     p = 2: witness 1, then decide (the local Fact instance is in the goal)                R28
     p odd: make p literally 2 * (2 * k) + 1 (witness p / 4; omega uses h and hm)         R29
       witness ((2 * k).factorial : ZMod (2 * (2 * k) + 1))                               refine ⟨_, ?_⟩
       Wilson for this p                                                                 R30
       in hw: 2 * (2 * k) + 1 - 1 → 2 * (2 * k), then `rw [half_factorial]`,
       then (-1) ^ (2 * k) → ((-1) ^ 2) ^ k → 1 ^ k → 1, drop `1 *`                      R31, half_factorial, R23, R32 → R33 → R34
       hw is now the goal
-/
-- BEGIN SPEC
theorem neg_one_sq_iff (p : ℕ) [Fact p.Prime] : (∃ x : ZMod p, x ^ 2 = -1) ↔ p % 4 ≠ 3 :=
-- END SPEC
  by
    constructor
    · rintro ⟨x, hx⟩ h3
      exact not_sq_of_three_mod_four p h3 x hx
    · intro h
      rcases (Fact.out : p.Prime).eq_two_or_odd' with rfl | ⟨m, hm⟩
      · -- WHY: plain `decide` fails here: the `Fact` instance is a local variable; `+revert` abstracts it.
        exact ⟨1, by decide +revert⟩
      obtain ⟨k, rfl⟩ : ∃ k, p = 2 * (2 * k) + 1 := ⟨p / 4, by omega⟩
      refine ⟨((2 * k).factorial : ZMod (2 * (2 * k) + 1)), ?_⟩
      have hw := ZMod.wilsons_lemma (p := 2 * (2 * k) + 1)
      rw [Nat.add_sub_cancel, half_factorial, pow_mul, neg_one_sq, one_pow, one_mul] at hw
      exact hw

end H034

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two milestones carry the work. (→) is Fermat: if `p % 4 = 3` then `p - 1 = 2 * (2k + 1)` and
    `x ^ (p - 1) = (x ^ 2) ^ (2k + 1) = (-1) ^ (2k + 1) = -1`, against `-1 ≠ 1`. (←) is Wilson: split off
    `p = 2`, write `p = 2 * (2k) + 1`, and take the witness `(2k)!`, using `half_factorial` with `n = 2k`.
H2. `half_factorial`: prove `h1` (the factorial split, R1–R3), `h2` (each `n + 1 + i` is `-(n - i)` in
    `ZMod (2n + 1)` because the two add up to the modulus, R5–R8) and `h3` (`∏ (n - i) = n!` by reversing
    the product, R9–R11), then rewrite the cast goal with them (R12–R16) and `ring`.
    `not_sq_of_three_mod_four`: `x ≠ 0` (R17, R18), the instance `Fact (2 < p)` (R19, R20), Fermat (R21),
    `p - 1 = 2 * (2k + 1)` (R22), then rewrite inside the Fermat fact (R23, R24) to get `-1 = 1` (R25).
    `neg_one_sq_iff`: `p = 2` by `⟨1, by decide +revert⟩` (R28); otherwise `obtain ⟨k, rfl⟩` (R29) and Wilson (R30).
H3. `h2`: `rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff,
    show n + 1 + i + (n - i) = 2 * n + 1 by omega]`; the main chain is
    `rw [h1, Nat.cast_mul, Nat.cast_prod, prod_congr rfl h2, prod_neg, card_range, ← Nat.cast_prod, h3]; ring`.
    Fermat side: `haveI : Fact (2 < p) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩` and
    `rw [hk, pow_mul, hx, (odd_two_mul_add_one k).neg_one_pow] at hfl`.
    Wilson side: `have hw := ZMod.wilsons_lemma (p := 2 * (2 * k) + 1)`, then
    `rw [Nat.add_sub_cancel, half_factorial, pow_mul, neg_one_sq, one_pow, one_mul] at hw`.
-/

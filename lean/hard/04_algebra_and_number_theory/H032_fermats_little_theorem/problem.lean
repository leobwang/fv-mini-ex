/- H032 | Fermat's little theorem | 30-45 min | binomial theorem, Nat.ModEq, induction, Finset.sum, mathlib
GOAL
  For a prime `p`, prove `a ^ p ≡ a (mod p)` from the binomial theorem ("freshman's dream"
  `(a + 1) ^ p ≡ a ^ p + 1`) and induction on `a`; then cancel `a` when `p ∤ a`.

BANNED: exact?, apply?, rw?, hint, try?
BANNED: ZMod, Fact, CharP, ExpChar, GaloisField, IsCoprime, frobenius, ZMod.frobenius_zmod, ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff', ZMod.intCast_eq_intCast_iff, add_pow_char, add_pow_char_of_commute, add_pow_expChar, add_pow_prime_eq, add_pow_prime_eq', add_pow_prime_pow_eq, add_pow_prime_pow_eq', exists_add_pow_prime_eq, exists_add_pow_prime_pow_eq, Nat.Prime.dvd_add_pow_sub_pow_of_dvd
BANNED: ZMod.pow_card, ZMod.pow_card_sub_one, ZMod.pow_card_sub_one_eq_one, Nat.ModEq.pow_card_sub_one_eq_one, Int.ModEq.pow_card_sub_one_eq_one, Int.ModEq.pow_prime_eq_self, Int.ModEq.pow_eq_pow, Int.prime_dvd_pow_self_sub, Int.prime_dvd_pow_sub_one, Nat.ModEq.pow_totient, ZMod.pow_totient, Nat.pow_totient_mod_eq_one, Nat.pow_totient_mod, Nat.pow_card_sub_one_sub_one_mod_card, pow_card_eq_one, pow_card_eq_one', ZMod.orderOf_dvd_card_sub_one

GUIDE
  Entries R1–R32: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H032

/- SKELETON · middle_terms   (milestone; prove it FIRST; freshman uses it for the middle of the sum)
  1. A prime divides a sum if it divides every term:                                   R1
  2. Introduce the index and its membership; turn `i ∈ range q` into `i < q`:          R2, R3
  3. The term is `a ^ (i + 1) * (q + 1).choose (i + 1)`. Drop the factor `a ^ (i + 1)`:   R7
     then the prime divides the binomial factor, since `i + 1 ≠ 0` and `i + 1 < q + 1`:  R4 (side goals: R5, R6)
     (As one term the order flips: R4's proof first, then `.mul_left _` on it.)
-/
-- MILESTONE (optional: change or delete)
theorem middle_terms (q a : ℕ) (hp : (q + 1).Prime) :
    q + 1 ∣ ∑ i ∈ Finset.range q, a ^ (i + 1) * (q + 1).choose (i + 1) := by
  sorry

/- SKELETON · freshman   (milestone; prove it after middle_terms; fermat uses it in the succ case)
  1. Get `1 < p`, then write `p = q + 1` so that both end terms can be peeled:          R8, R9
  2. Expand, peel the last term, then the first:                                       R10, R11, R12
  3. Clean the end terms and the `1 ^ _`, `↑` in the middle, in one `simp only`:       R13–R19
     the goal is now   middle + 1 + a ^ (q + 1) ≡ a ^ (q + 1) + 1 [MOD q + 1]
     with `middle` exactly the sum of middle_terms.
  4. hmid : middle ≡ 0 [MOD q + 1]   from the milestone middle_terms:                   R20
  5. Finish with a calc:  _ ≡ 0 + 1 + a ^ (q + 1)   (add `1`, then `a ^ (q + 1)`)        R22, R21
                            _ = a ^ (q + 1) + 1                                        R23
-/
-- MILESTONE (optional: change or delete)
theorem freshman (p a : ℕ) (hp : p.Prime) : (a + 1) ^ p ≡ a ^ p + 1 [MOD p] := by
  sorry

/- SKELETON · fermat
  0. Uses the milestone freshman (which uses middle_terms) in step 3.
  1. Induction on `a`, naming the successor case `a ih`:                                R24
  2. zero: `0 ^ p ≡ 0`; rewrite `0 ^ p` with `0 < p`, `rw` closes the rest:             R25, R26
  3. succ: `(a + 1) ^ p ≡ a ^ p + 1` (freshman) then `≡ a + 1` (the IH plus 1):          R27, R21
-/
-- BEGIN SPEC
theorem fermat (p a : ℕ) (hp : p.Prime) : a ^ p ≡ a [MOD p] :=
-- END SPEC
  sorry

/- SKELETON · fermat'
  0. Uses fermat in step 4.
  1. `¬p ∣ a` → `p.Coprime a`, and cancel the factor `a`:                               R28, R29
       goal:  a * a ^ (p - 1) ≡ a * 1 [MOD p]
  2. Fold `a * a ^ (p - 1)` into `a ^ (p - 1 + 1)`:                                     R30
  3. `p - 1 + 1 = p` needs `1 ≤ p` (truncated subtraction); then drop `* 1`:            R8, R31, R32, R14
  4. The goal is `a ^ p ≡ a [MOD p]`: that is fermat.                                   exact
-/
-- BEGIN SPEC
theorem fermat' (p a : ℕ) (hp : p.Prime) (ha : ¬ p ∣ a) : a ^ (p - 1) ≡ 1 [MOD p] :=
-- END SPEC
  sorry

end H032

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Binomial theorem: `(a + 1) ^ p = ∑ₖ a ^ k * C(p, k)`. The `k = 0` and `k = p` terms are `1` and
    `a ^ p`; `p` divides every `C(p, k)` with `0 < k < p` (R4). That is `freshman`; `fermat` follows by
    induction on `a` (R24). For `fermat'`, cancel one factor `a`, coprime to `p` (R28, R29).
H2. `middle_terms`: `Finset.dvd_sum` (R1), then each term by R4 and `.mul_left` (R7). `freshman`: write
    `p = q + 1` first (R8, R9), then `rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']` and one
    `simp only` with R13–R19; the middle sum is `≡ 0` (R20) and a `calc` with `.add_right` (R21, R22) ends it.
    `fermat`: zero case `rw [Nat.zero_pow hp.pos]`; succ case glue `freshman` and the IH with `.trans` (R27).
H3. `freshman`: `have hmid := Nat.modEq_zero_iff_dvd.mpr (middle_terms q a hp)`, then
    `calc _ ≡ 0 + 1 + a ^ (q + 1) [MOD q + 1] := (hmid.add_right 1).add_right _` and `_ = … := by ring`.
    `fermat` succ: `exact (freshman p a hp).trans (ih.add_right 1)`.
    `fermat'`: `apply Nat.ModEq.cancel_left_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha)`; then
    one `rw` with R30, R32 (argument `hp.one_lt.le`) and R14 turns the goal into `fermat p a hp`.
-/

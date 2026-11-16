/- H032 | Fermat's little theorem | 30-45 min | binomial theorem, Nat.ModEq, induction, Finset.sum, mathlib
GOAL
  For a prime `p`, prove `a ^ p ≡ a (mod p)` from the binomial theorem ("freshman's dream"
  `(a + 1) ^ p ≡ a ^ p + 1`) and induction on `a`; then cancel `a` when `p ∤ a`.

REFERENCE
  #check add_pow   -- (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m
  #check Finset.sum_range_succ   -- ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n
  #check Finset.sum_range_succ'  -- ∑ i ∈ range (n + 1), f i = ∑ i ∈ range n, f (i + 1) + f 0
  #check Nat.Prime.dvd_choose_self  -- p.Prime → k ≠ 0 → k < p → p ∣ p.choose k
  #check Finset.dvd_sum            -- (∀ i ∈ s, a ∣ f i) → a ∣ ∑ i ∈ s, f i
  #check Nat.modEq_zero_iff_dvd     -- a ≡ 0 [MOD n] ↔ n ∣ a
  #check Nat.ModEq.cancel_left_of_coprime  -- m.gcd c = 1 → c * a ≡ c * b [MOD m] → a ≡ b [MOD m]
  #check Nat.Prime.coprime_iff_not_dvd     -- p.Prime → (p.Coprime n ↔ ¬p ∣ n); `p.Coprime n` unfolds to `p.gcd n = 1`
  example (n a b c : ℕ) (h : a ≡ b [MOD n]) : a + c ≡ b + c [MOD n] := h.add_right c  -- also `.trans`, `.symm`
  -- `a ≡ b [MOD n]` is `Nat.ModEq n a b`, i.e. `a % n = b % n`; `n.choose k` is the binomial coefficient.
BANNED: exact?, apply?, rw?, hint, try?
BANNED: ZMod, Fact, CharP, ExpChar, GaloisField, IsCoprime, frobenius, ZMod.frobenius_zmod, ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff', ZMod.intCast_eq_intCast_iff, add_pow_char, add_pow_char_of_commute, add_pow_expChar, add_pow_prime_eq, add_pow_prime_eq', add_pow_prime_pow_eq, add_pow_prime_pow_eq', exists_add_pow_prime_eq, exists_add_pow_prime_pow_eq, Nat.Prime.dvd_add_pow_sub_pow_of_dvd
BANNED: ZMod.pow_card, ZMod.pow_card_sub_one, ZMod.pow_card_sub_one_eq_one, Nat.ModEq.pow_card_sub_one_eq_one, Int.ModEq.pow_card_sub_one_eq_one, Int.ModEq.pow_prime_eq_self, Int.ModEq.pow_eq_pow, Int.prime_dvd_pow_self_sub, Int.prime_dvd_pow_sub_one, Nat.ModEq.pow_totient, ZMod.pow_totient, Nat.pow_totient_mod_eq_one, Nat.pow_totient_mod, Nat.pow_card_sub_one_sub_one_mod_card, pow_card_eq_one, pow_card_eq_one', ZMod.orderOf_dvd_card_sub_one
NOTE: `ZMod`, characteristic-`p` rings and library binomial-mod-`p` lemmas (`add_pow_prime_eq`) are banned: the point is the binomial-theorem proof by hand.
-/
import Mathlib

namespace H032

-- MILESTONE (optional: change or delete)
theorem middle_terms (q a : ℕ) (hp : (q + 1).Prime) :
    q + 1 ∣ ∑ i ∈ Finset.range q, a ^ (i + 1) * (q + 1).choose (i + 1) := by
  apply Finset.dvd_sum
  intro i hi
  rw [Finset.mem_range] at hi
  exact (hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)).mul_left _

-- MILESTONE (optional: change or delete)
theorem freshman (p a : ℕ) (hp : p.Prime) : (a + 1) ^ p ≡ a ^ p + 1 [MOD p] := by
  have := hp.one_lt
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [one_pow, mul_one, Nat.choose_self, Nat.sub_self, pow_zero, Nat.choose_zero_right,
    Nat.cast_id]
  have hmid := Nat.modEq_zero_iff_dvd.mpr (middle_terms q a hp)
  calc _ ≡ 0 + 1 + a ^ (q + 1) [MOD q + 1] := (hmid.add_right 1).add_right _
    _ = a ^ (q + 1) + 1 := by ring

-- BEGIN SPEC
theorem fermat (p a : ℕ) (hp : p.Prime) : a ^ p ≡ a [MOD p] :=
-- END SPEC
  by
    induction a with
    | zero => rw [Nat.zero_pow hp.pos]
    | succ a ih => exact (freshman p a hp).trans (ih.add_right 1)

-- BEGIN SPEC
theorem fermat' (p a : ℕ) (hp : p.Prime) (ha : ¬ p ∣ a) : a ^ (p - 1) ≡ 1 [MOD p] :=
-- END SPEC
  by
    apply Nat.ModEq.cancel_left_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha)
    -- WHY: `p - 1` is truncated subtraction; `Nat.sub_add_cancel` needs `1 ≤ p`.
    rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, mul_one]
    exact fermat p a hp

end H032

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `(a + 1) ^ p = ∑ C(p, k) a^k`: the `k = 0` and `k = p` terms give `1 + a ^ p`, and `p` divides
    every `C(p, k)` in between. Fermat then follows by induction on `a`.
H2. In `freshman`, write `p = q + 1` (`obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩` after
    `have := hp.one_lt`), then `rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']` peels off
    both end terms; `simp only [one_pow, mul_one, Nat.choose_self, ...]` cleans them up.
    The middle sum is `≡ 0`, by `Finset.dvd_sum` and `Dvd.dvd.mul_left (hp.dvd_choose_self ...) _`.
H3. `fermat`: `induction a with | zero => rw [Nat.zero_pow hp.pos] | succ a ih => exact (freshman p a hp).trans (ih.add_right 1)`.
    `fermat'`: `apply Nat.ModEq.cancel_left_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha)`;
    the goal `a * a ^ (p - 1) ≡ a * 1` is `fermat` after `pow_succ'` and `Nat.sub_add_cancel`.
-/

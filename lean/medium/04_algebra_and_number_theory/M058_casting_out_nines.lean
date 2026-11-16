/- M058 | Casting out nines | 10-15 min | Nat.ModEq, Nat.digits, strong induction, calc, mathlib
GOAL
  Prove `10 ^ k ≡ 1 (mod 9)`, then that every `n` is congruent mod 9 to the sum of its decimal
  digits, and derive the test "9 ∣ n iff 9 divides the digit sum".
  `Nat.digits 10 n` lists the digits of `n`, least significant first: `Nat.digits 10 123 = [3, 2, 1]`.

REFERENCE
  example : 10 ≡ 1 [MOD 9] := by decide   -- `a ≡ b [MOD n]` is `Nat.ModEq n a b`, i.e. a % n = b % n
  example (a b n k : ℕ) (h : a ≡ b [MOD n]) : a ^ k ≡ b ^ k [MOD n] := h.pow k   -- `.symm`, `.trans` too
  #check Nat.ModEq.add_left    -- (c : ℕ) → a ≡ b [MOD n] → c + a ≡ c + b [MOD n]
  #check Nat.ModEq.mul_right   -- (c : ℕ) → a ≡ b [MOD n] → a * c ≡ b * c [MOD n]
  #check Nat.digits_def'       -- 1 < b → 0 < n → b.digits n = n % b :: b.digits (n / b)
  #check Nat.mod_add_div       -- m % k + k * (m / k) = m
  #check Nat.div_lt_self       -- 0 < n → 1 < k → n / k < n
  #check Nat.modEq_zero_iff_dvd   -- a ≡ 0 [MOD n] ↔ n ∣ a
  -- `induction n using Nat.strong_induction_on with | _ n ih => ...`  (ih : ∀ m < n, P m)
  -- `calc` chains `_ ≡ _ [MOD 9]` steps, each justified by a ModEq term.
BANNED: Nat.modEq_nine_digits_sum, Nat.nine_dvd_iff, Nat.modEq_digits_sum, Nat.modEq_three_digits_sum, Nat.three_dvd_iff, Nat.dvd_iff_dvd_digits_sum, Nat.modEq_eleven_digits_sum, Nat.dvd_iff_dvd_ofDigits, Nat.ofDigits, Nat.ofDigits_digits, Nat.ofDigits_modEq, Nat.ofDigits_modEq', Nat.ofDigits_mod, Nat.ofDigits_zmodeq, Nat.ofDigits_zmodeq', Nat.zmodeq_ofDigits_digits, Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits, Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, exact?, apply?, rw?, hint, try?
NOTE: search tactics (`exact?`, `try?`, ...) are fine for exploring, but they close goals with banned lemmas, so they cannot stay.
-/
import Mathlib

namespace M058

-- BEGIN SPEC
theorem ten_pow_modEq (k : ℕ) : 10 ^ k ≡ 1 [MOD 9] :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem digits_sum_modEq (n : ℕ) : n ≡ (Nat.digits 10 n).sum [MOD 9] :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem nine_dvd_iff_digits (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum :=
-- END SPEC
  sorry

end M058

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ten_pow_modEq` is one `.pow` away from `10 ≡ 1 [MOD 9]` (then tidy `1 ^ k` with `simpa`). For the
    digit sum, peel off the last digit: `n = n % 10 + 10 * (n / 10)`, and `n / 10 < n` when `n > 0`.
H2. Strong induction on `n`. Case `n = 0` is `rfl`. Otherwise rewrite with `Nat.digits_def'` and
    `List.sum_cons`, then a 3-step `calc`: split `n`, replace `10` by `1`, use the IH on `n / 10`.
    For the test, turn both `9 ∣ _` into `_ ≡ 0 [MOD 9]` and chain with `digits_sum_modEq`.
H3. With `h10 : 10 ≡ 1 [MOD 9]` and `hlt : n / 10 < n`:
    `calc n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
      _ ≡ n % 10 + 1 * (n / 10) [MOD 9] := (h10.mul_right _).add_left _
      _ ≡ n % 10 + (Nat.digits 10 (n / 10)).sum [MOD 9] := by rw [one_mul]; exact (ih _ hlt).add_left _`;
    test: `rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]`, then `(digits_sum_modEq n).symm.trans h`.
-/

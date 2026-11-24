/- M058 | Casting out nines | 10-15 min | Nat.ModEq, Nat.digits, strong induction, calc, mathlib
GOAL
  Prove `10 ^ k ≡ 1 (mod 9)`, then that every `n` is congruent mod 9 to the sum of its decimal digits
  (`Nat.digits 10 n`, least significant first: `Nat.digits 10 123 = [3, 2, 1]`), and derive the test
  "9 ∣ n iff 9 divides the digit sum".
BANNED: Nat.modEq_nine_digits_sum, Nat.nine_dvd_iff, Nat.modEq_digits_sum, Nat.modEq_three_digits_sum, Nat.three_dvd_iff, Nat.dvd_iff_dvd_digits_sum, Nat.modEq_eleven_digits_sum, Nat.dvd_iff_dvd_ofDigits, Nat.ofDigits, Nat.ofDigits_digits, Nat.ofDigits_modEq, Nat.ofDigits_modEq', Nat.ofDigits_mod, Nat.ofDigits_zmodeq, Nat.ofDigits_zmodeq', Nat.zmodeq_ofDigits_digits, Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits, Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, exact?, apply?, rw?, hint, try?

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M058

/- SKELETON · ten_pow_modEq
  1. The base fact `h : 10 ≡ 1 [MOD 9]`, by computation:                   R2
  2. Raise both sides to the power `k`: `10 ^ k ≡ 1 ^ k [MOD 9]`:           R3
  3. Let `simp` turn `1 ^ k` into `1`, and close with that term:           R4
-/
-- BEGIN SPEC
theorem ten_pow_modEq (k : ℕ) : 10 ^ k ≡ 1 [MOD 9] :=
-- END SPEC
  sorry

/- SKELETON · digits_sum_modEq
  1. Strong induction on `n`, so that the claim for `n / 10` is available:  R5
       ih : ∀ m < n, m ≡ (Nat.digits 10 m).sum [MOD 9]
  2. Split `n = 0` / `hn : n > 0`:                                          R6
  3. Case `n = 0`: both sides compute to `0`:                               R7
  4. Case `n > 0`: peel the last digit off the right side
     (`1 < 10` by `(by norm_num)`):                                         R8, R9
       goal  n ≡ n % 10 + (Nat.digits 10 (n / 10)).sum [MOD 9]
  5. Facts for later:  hlt : n / 10 < n                                     R10
                       h10 : 10 ≡ 1 [MOD 9]                                 R2
  6. A three-step `calc` from `n` to the goal's right side:                 R11
       n = n % 10 + 10 * (n / 10)                                           R12
       _ ≡ n % 10 + 1 * (n / 10)  [MOD 9]       from h10                    R13 → R14
       _ ≡ n % 10 + (Nat.digits 10 (n / 10)).sum  [MOD 9]
                                  drop `1 *`, then `ih` at `n / 10` (hlt)   R15, R14
-/
-- BEGIN SPEC
theorem digits_sum_modEq (n : ℕ) : n ≡ (Nat.digits 10 n).sum [MOD 9] :=
-- END SPEC
  sorry

/- SKELETON · nine_dvd_iff_digits
  Uses Part 2: `digits_sum_modEq n : n ≡ (Nat.digits 10 n).sum [MOD 9]`, applied as a term.
  1. Both divisibilities → congruences with `0` (one rewrite each):        R16, R16
  2. Split the `↔`, naming the assumption `h` in each direction:            R17
  3. →  (h : n ≡ 0 [MOD 9]): flip `digits_sum_modEq n`, chain with `h`:      R18 → R19
  4. ←  (h : (Nat.digits 10 n).sum ≡ 0 [MOD 9]): chain `digits_sum_modEq n`
        with `h`:                                                           R19
-/
-- BEGIN SPEC
theorem nine_dvd_iff_digits (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum :=
-- END SPEC
  sorry

end M058

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ten_pow_modEq` is one `.pow` away from `10 ≡ 1 [MOD 9]`. For the digit sum, peel off the last digit:
    `n = n % 10 + 10 * (n / 10)` with `10 ≡ 1`, and `n / 10 < n` when `n > 0`, so you need the claim for
    `n / 10`: strong induction. The test follows from the digit-sum congruence.
H2. Part 1: `10 ≡ 1 [MOD 9]` by `decide`, raise it with `.pow k`, finish with `simpa using …`.
    Part 2: `induction n using Nat.strong_induction_on with | _ n ih => …`, then
    `rcases Nat.eq_zero_or_pos n with rfl | hn`; case `0` is `rfl`; otherwise
    `rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]`, prove `hlt` and `h10`, then a 3-step `calc`.
    Part 3: `rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]`, then chain with `digits_sum_modEq n`.
H3. Part 1: `simpa using (show 10 ≡ 1 [MOD 9] by decide).pow k`. Part 2, the `calc`:
    `calc n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
      _ ≡ n % 10 + 1 * (n / 10) [MOD 9] := (h10.mul_right _).add_left _
      _ ≡ n % 10 + (Nat.digits 10 (n / 10)).sum [MOD 9] := by rw [one_mul]; exact (ih _ hlt).add_left _`.
    Part 3: after both rewrites and the `↔` split, the → direction is `(digits_sum_modEq n).symm.trans h`; ← is similar.
-/

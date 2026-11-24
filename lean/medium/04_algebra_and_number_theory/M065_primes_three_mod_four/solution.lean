/- M065 | Infinitely many primes ≡ 3 mod 4 | 15-20 min | Nat.mul_mod, interval_cases, factorial, nat subtraction, mathlib
GOAL
  Above every `n` there is a prime `p` with `p % 4 = 3`. Prove `mod4_of_mul` (if `a * b ≡ 3 mod 4`, one factor
  is `≡ 3 mod 4`), then apply the given lemma `exists_prime_three` to `4 * n.factorial - 1` (`n.factorial` is n!).

REFERENCE
  #check Nat.mul_mod          -- a * b % n = (a % n) * (b % n) % n
  example (a : ℕ) : a % 4 < 4 := Nat.mod_lt a (by norm_num)
  -- `interval_cases a % 4` splits into the cases `a % 4 = 0, 1, 2, 3` (needs a bound like the line above)
  #check Nat.factorial_pos    -- 0 < n.factorial
  #check Nat.dvd_factorial    -- 0 < m → m ≤ n → m ∣ n.factorial
  #check dvd_mul_of_dvd_right -- a ∣ b → ∀ c, a ∣ c * b
  #check Nat.dvd_sub          -- k ∣ m → k ∣ n → k ∣ m - n
  #check Nat.Prime.one_lt     -- p.Prime → 1 < p;   `Nat.dvd_one : n ∣ 1 ↔ n = 1`
NOTE: `4 * n.factorial - 1` is truncated ℕ subtraction; `omega` with `Nat.factorial_pos n` in context handles it.
BANNED: Nat.forall_exists_prime_gt_and_modEq, Nat.forall_exists_prime_gt_and_eq_mod, Nat.forall_exists_prime_gt_and_zmodEq
BANNED: Nat.infinite_setOf_prime_and_modEq, Nat.infinite_setOf_prime_and_eq_mod, Nat.frequently_atTop_prime_and_modEq, Filter, Frequently
-/
import Mathlib

namespace M065

-- BEGIN SPEC
theorem mod4_of_mul (a b : ℕ) (h : a * b % 4 = 3) : a % 4 = 3 ∨ b % 4 = 3 :=
-- END SPEC
  by
    rw [Nat.mul_mod] at h
    have ha : a % 4 < 4 := Nat.mod_lt a (by norm_num)
    have hb : b % 4 < 4 := Nat.mod_lt b (by norm_num)
    interval_cases a % 4 <;> interval_cases b % 4 <;> simp_all

/-- Given (proved here, frozen): every `m ≡ 3 mod 4` has a prime factor `≡ 3 mod 4`. Strong induction on `m`:
if `m` is not prime, split `m = a * b` with `2 ≤ a, b`; by `mod4_of_mul` one factor is `≡ 3 mod 4`, recurse. -/
-- BEGIN SPEC
theorem exists_prime_three (m : ℕ) (hm : m % 4 = 3) : ∃ p, p.Prime ∧ p ∣ m ∧ p % 4 = 3 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hp : m.Prime
    · exact ⟨m, hp, dvd_refl m, hm⟩
    · obtain ⟨a, ha, ha1, ham⟩ : ∃ a, a ∣ m ∧ a ≠ 1 ∧ a ≠ m := by
        rw [Nat.prime_def] at hp
        push Not at hp
        exact hp (by omega)
      obtain ⟨b, rfl⟩ := ha
      have ha0 : a ≠ 0 := by rintro rfl; simp at hm
      have hb0 : b ≠ 0 := by rintro rfl; simp at hm
      have hb1 : b ≠ 1 := by rintro rfl; simp at ham
      have hlta : a < a * b := by nlinarith [Nat.pos_of_ne_zero ha0, show 2 ≤ b by omega]
      have hltb : b < a * b := by nlinarith [Nat.pos_of_ne_zero hb0, show 2 ≤ a by omega]
      rcases mod4_of_mul a b hm with h | h
      · obtain ⟨p, hp, hpd, hp4⟩ := ih a hlta h
        exact ⟨p, hp, hpd.trans (dvd_mul_right a b), hp4⟩
      · obtain ⟨p, hp, hpd, hp4⟩ := ih b hltb h
        exact ⟨p, hp, hpd.trans (dvd_mul_left b a), hp4⟩
-- END SPEC

-- BEGIN SPEC
theorem primes_three_mod_four (n : ℕ) : ∃ p, n < p ∧ p.Prime ∧ p % 4 = 3 :=
-- END SPEC
  by
    have hf := Nat.factorial_pos n
    obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_three (4 * n.factorial - 1) (by omega)
    refine ⟨p, ?_, hp, hp4⟩
    by_contra hle
    push Not at hle
    have h1 : p ∣ 4 * n.factorial := dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hle) 4
    have h2 := Nat.dvd_sub h1 hpd
    -- WHY: ℕ subtraction; `4 * n! - (4 * n! - 1) = 1` only because `4 * n! ≥ 1`.
    rw [show 4 * n.factorial - (4 * n.factorial - 1) = 1 by omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

end M065

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `mod4_of_mul` is a finite check on the residues `a % 4` and `b % 4`. Main: Euclid's argument. A prime
    `p ∣ 4 * n.factorial - 1` with `p ≤ n` would also divide `4 * n.factorial`, hence their difference `1`.
H2. `mod4_of_mul`: `rw [Nat.mul_mod] at h`, put `a % 4 < 4` and `b % 4 < 4` in context, then
    `interval_cases a % 4 <;> interval_cases b % 4 <;> simp_all`.
    Main: get `p` from `exists_prime_three`, `refine ⟨p, ?_, hp, hp4⟩`, then `by_contra hle; push Not at hle`.
H3. Main: `obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_three (4 * n.factorial - 1) (by omega)`; for `p ≤ n`,
    `Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hle) 4) hpd : p ∣ 4 * n.factorial - (4 * n.factorial - 1)`,
    and that number is `1` (`omega`).
-/

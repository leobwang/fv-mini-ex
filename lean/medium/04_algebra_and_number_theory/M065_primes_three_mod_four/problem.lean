/- M065 | Infinitely many primes ≡ 3 mod 4 | 15-20 min | Nat.mul_mod, interval_cases, factorial, nat subtraction, mathlib
GOAL
  Above every `n` there is a prime `p` with `p % 4 = 3`. Prove `mod4_of_mul` (if `a * b ≡ 3 mod 4`, one factor
  is `≡ 3 mod 4`), then apply the given lemma `exists_prime_three` to `4 * n.factorial - 1` (`n.factorial` is n!).
BANNED: Nat.forall_exists_prime_gt_and_modEq, Nat.forall_exists_prime_gt_and_eq_mod, Nat.forall_exists_prime_gt_and_zmodEq
BANNED: Nat.infinite_setOf_prime_and_modEq, Nat.infinite_setOf_prime_and_eq_mod, Nat.frequently_atTop_prime_and_modEq, Filter, Frequently

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M065

/- SKELETON · mod4_of_mul
  1. Rewrite `h` into residue form `a % 4 * (b % 4) % 4 = 3`:              R1
  2. Put the bounds `a % 4 < 4` and `b % 4 < 4` in the context
     (`0 < 4` by `(by norm_num)`):                                         R2, R2
  3. Split on both residues, chained with `<;>` (16 goals):                R3, R3
  4. Close every goal: either `h` is false arithmetic or a disjunct
     is `3 = 3`:                                                           R4
-/
-- BEGIN SPEC
theorem mod4_of_mul (a b : ℕ) (h : a * b % 4 = 3) : a % 4 = 3 ∨ b % 4 = 3 :=
-- END SPEC
  sorry

/- SKELETON · exists_prime_three   (GIVEN: proved and frozen, nothing to fill)
  Every `m ≡ 3 mod 4` has a prime factor `≡ 3 mod 4`. Strong induction on `m`: if `m` is prime, take
  `p = m`; otherwise `m = a * b` with `2 ≤ a, b`, `mod4_of_mul a b hm` says one factor is `≡ 3 mod 4`,
  and the induction hypothesis applies to it. It uses `mod4_of_mul`, so `./check` counts it as open
  until that is proved. In `primes_three_mod_four` you only apply it as a term (R7).
-/
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

/- SKELETON · primes_three_mod_four
  1. `hf : 0 < n.factorial`; every `omega` below needs it (truncated `-`):  R5
  2. A prime `p ∣ 4 * n.factorial - 1` with `p % 4 = 3`: apply the given
     `exists_prime_three`; its hypothesis `(… - 1) % 4 = 3` by `omega`:    R7, R6
  3. Give `p` and the facts you already have; `n < p` is left:             R8
  4. Suppose not; turn `¬n < p` into `hle : p ≤ n`:                         R9, R10
  5. `h1 : p ∣ 4 * n.factorial` (first `p ∣ n.factorial`):                  R11 → R12 → R13
  6. `h2 : p ∣ 4 * n.factorial - (4 * n.factorial - 1)`:                    R14
  7. Rewrite that number to `1` in `h2`:                                    R15 (with R6)
  8. `p ∣ 1` gives `p = 1`, against `1 < p`:                                R16, R17 → R18
-/
-- BEGIN SPEC
theorem primes_three_mod_four (n : ℕ) : ∃ p, n < p ∧ p.Prime ∧ p % 4 = 3 :=
-- END SPEC
  sorry

end M065

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `mod4_of_mul`: `a * b % 4` depends only on `a % 4` and `b % 4`, so it is a check of 16 residue pairs.
    Main: Euclid's argument with `N = 4 * n.factorial - 1`. A prime `p ∣ N` with `p ≤ n` also divides
    `4 * n.factorial`, hence their difference, which is `1`.
H2. `mod4_of_mul`: `rw [Nat.mul_mod] at h`, put `a % 4 < 4` and `b % 4 < 4` in context (`Nat.mod_lt`), then
    `interval_cases a % 4 <;> interval_cases b % 4 <;> simp_all`.
    Main: `have hf := Nat.factorial_pos n` first; get `p` from `exists_prime_three`;
    `refine ⟨p, ?_, hp, hp4⟩`; `by_contra hle; push Not at hle`.
H3. Main: `obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_three (4 * n.factorial - 1) (by omega)`; for `p ≤ n`,
    `Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hle) 4) hpd : p ∣ 4 * n.factorial - (4 * n.factorial - 1)`;
    `rw [show 4 * n.factorial - (4 * n.factorial - 1) = 1 by omega] at h2`, then `Nat.dvd_one`, `hp.one_lt.ne'`.
-/

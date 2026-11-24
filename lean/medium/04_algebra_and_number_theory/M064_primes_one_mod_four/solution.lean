/- M064 | Infinitely many primes ≡ 1 mod 4 | 15-20 min | ZMod, casts, Fact, Nat.Prime, mathlib
GOAL
  Above every `n` there is a prime `p` with `p % 4 = 1`. Take a prime factor `p` of `(2 * n.factorial)^2 + 1`
  (`n.factorial` is n!). Then `-1` is a square in `ZMod p` (so `p % 4 ≠ 3`, a library fact), `p` is odd,
  and `p > n`.
BANNED: Nat.forall_exists_prime_gt_and_modEq, Nat.forall_exists_prime_gt_and_eq_mod, Nat.forall_exists_prime_gt_and_zmodEq
BANNED: Nat.infinite_setOf_prime_and_modEq, Nat.infinite_setOf_prime_and_eq_mod, Nat.frequently_atTop_prime_and_modEq
BANNED: Nat.exists_prime_gt_modEq_one, Nat.infinite_setOf_prime_modEq_one, Nat.frequently_atTop_modEq_one, Filter, Frequently

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M064

/- SKELETON · primes_one_mod_four
  Build the prime and its three facts as `have`s first, then give the witness.
  1. hf : 0 < n.factorial                                                     R1
  2. A prime factor of N = (2 * n.factorial) ^ 2 + 1:                          R2
       p, hp : Nat.Prime p, hpd : p ∣ (2 * n.factorial) ^ 2 + 1
       name the implicit argument (n := N); its side goal N ≠ 1 from hf:       R3
  3. The instance `Fact (Nat.Prime p)`:                                        R4
  4. hsq : ((2 * n.factorial : ℕ) : ZMod p) ^ 2 = -1
       y ^ 2 = -1 → y ^ 2 + 1 = 0, then close it with the cast of hpd:        R5, R6 → R7
  5. h3 : p % 4 ≠ 3 from hsq:                                                  R8
  6. hp2 : p ≠ 2: substitute p := 2, prove 2 ∣ (2 * n.factorial) ^ 2,
     contradict hpd:                                                           R9, R10, R11
  7. Witness p, fill `Nat.Prime p` with hp; two goals remain:                  R12
  8. Goal n < p: assume the negation, turn it into p ≤ n:                       R13, R14
       h1 : p ∣ (2 * n.factorial) ^ 2, built inside out:                       R15, R16 → R17 → R18
       drop that summand from hpd, get p = 1, contradict 1 < p:               R19 → R20 → R15, R21
  9. Goal p % 4 = 1: split p = 2 ∨ p % 2 = 1:                                  R22
       p = 2 contradicts hp2:                                                  R23
       p % 2 = 1 together with h3:                                             R11
-/
-- BEGIN SPEC
theorem primes_one_mod_four (n : ℕ) : ∃ p, n < p ∧ p.Prime ∧ p % 4 = 1 :=
-- END SPEC
  by
    have hf := Nat.factorial_pos n
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := (2 * n.factorial) ^ 2 + 1) (by nlinarith)
    haveI := Fact.mk hp
    -- WHY: cast the ℕ number `2 * n!` as a whole; `exact_mod_cast` then matches it with `↑((2 * n!)^2 + 1) = 0`.
    have hsq : ((2 * n.factorial : ℕ) : ZMod p) ^ 2 = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact_mod_cast (ZMod.natCast_eq_zero_iff _ p).mpr hpd
    have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ (2 * n.factorial) ^ 2 := ⟨2 * n.factorial ^ 2, by ring⟩
      omega
    refine ⟨p, ?_, hp, ?_⟩
    · by_contra hle
      push Not at hle
      have h1 : p ∣ (2 * n.factorial) ^ 2 :=
        dvd_pow (dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hle) 2) two_ne_zero
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hpd))
    · rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · omega

end M064

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Take a prime `p ∣ (2 * n.factorial) ^ 2 + 1`. Three facts about it do all the work: `p % 4 ≠ 3`
    (`-1` is a square mod `p`), `p ≠ 2` (the number is odd), and `¬ p ≤ n` (else `p ∣ 1`).
    With `p % 2 = 1` they force `p % 4 = 1` (`omega`).
H2. Get `p` from `Nat.exists_prime_and_dvd (n := …) (by nlinarith)` (R2, R3). For `p % 4 ≠ 3`:
    `haveI := Fact.mk hp`, prove `((2 * n.factorial : ℕ) : ZMod p) ^ 2 = -1` from `hpd` via
    `ZMod.natCast_eq_zero_iff`, and apply `ZMod.mod_four_ne_three_of_sq_eq_neg_one`. For `n < p`:
    `by_contra`, `push Not`, then `p ∣ (2 * n.factorial) ^ 2`, `Nat.dvd_add_right`, `Nat.dvd_one`.
    Finish with `rcases hp.eq_two_or_odd with h | h`.
H3. `have hsq : ((2 * n.factorial : ℕ) : ZMod p) ^ 2 = -1 := by
       rw [eq_neg_iff_add_eq_zero]; exact_mod_cast (ZMod.natCast_eq_zero_iff _ p).mpr hpd`
    and, after `p ≤ n`:
    `have h1 : p ∣ (2 * n.factorial) ^ 2 :=
       dvd_pow (dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hle) 2) two_ne_zero`.
-/

/- H029 | Infinitely many primes | 45-60 min | strong induction, Nat.Prime, factorial, mathlib
GOAL
  Prove from scratch that above every `n` there is a prime: first that every `n ≥ 2` has a prime
  factor (strong induction), then Euclid's argument with `n! + 1`.

BANNED: Nat.exists_infinite_primes, Nat.minFac, Nat.minFac_prime, Nat.minFac_dvd, Nat.exists_prime_and_dvd, Nat.infinite_setOf_prime, Nat.primeFactors, Nat.primeFactorsList, Nat.not_bddAbove_setOf_prime

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H029

/- SKELETON · exists_prime_dvd   (milestone; prove it FIRST; infinitely_many_primes uses it in step 1)
  1. Strong induction on `n`, naming the number `n` and the IH `ih`. `hn : 2 ≤ n` comes back,
     and the IH also asks for it:  ih : ∀ m < n, 2 ≤ m → ∃ p, Nat.Prime p ∧ p ∣ m            R1
  2. Case on whether `n` is prime:                                                          R2
  3. `n` prime: `n` itself is the prime factor:                                             R3 with R4
  4. `n` not prime: a divisor that is neither 1 nor n,
       obtain ⟨m, hmn, hm1, hmn'⟩ : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n                             R5
     proof: unfold primality in `hp`, push the `¬` in, apply the implication to `hn`:      R6 → R7 → exact
  5. hm0 : m ≠ 0     (m = 0 turns hmn into 0 ∣ n, i.e. n = 0, against hn):                  R8 → R9 → R10
  6. hmlt : m < n    (m ≤ n since 0 < n, then strict since m ≠ n):                          R12 with R11, R10
  7. IH at `m` (its `2 ≤ m` from hm0, hm1); obtain p, hp, hpm : p ∣ m:                      R13, R10, R5
  8. p is the prime factor of n, since p ∣ m ∣ n:                                           R3 with R14
-/
-- MILESTONE (optional: change or delete)
theorem exists_prime_dvd (n : ℕ) (hn : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · exact ⟨n, hp, dvd_refl n⟩
    · obtain ⟨m, hmn, hm1, hmn'⟩ : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
        rw [Nat.prime_def] at hp
        push Not at hp
        exact hp hn
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hmn
        omega
      have hmlt : m < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hmn) hmn'
      obtain ⟨p, hp, hpm⟩ := ih m hmlt (by omega)
      exact ⟨p, hp, dvd_trans hpm hmn⟩

/- SKELETON · infinitely_many_primes
  0. Uses the milestone exists_prime_dvd (step 1).
  1. A prime factor of n! + 1:
       obtain ⟨p, hp, hpd⟩ := exists_prime_dvd (n.factorial + 1) (proof of 2 ≤ n.factorial + 1)
     the side proof: R15, then R10                                                          R5, R15 → R10
  2. Witness `p`, primality is `hp`; the goal left is `n ≤ p`:                              R16
  3. Suppose not, and turn `¬n ≤ p` into `hlt : p < n`:                                     R17 → R7
  4. h1 : p ∣ n.factorial   (0 < p and p ≤ n):                                              R18 with R19, R20
  5. h2 : p ∣ 1             (p ∣ n! and p ∣ n! + 1):                                        R21
  6. `p = 1` contradicts `1 < p`:                                                           R24, R22 → R23
-/
-- BEGIN SPEC
theorem infinitely_many_primes (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
-- END SPEC
  by
    obtain ⟨p, hp, hpd⟩ :=
      exists_prime_dvd (n.factorial + 1) (by have := Nat.factorial_pos n; omega)
    refine ⟨p, ?_, hp⟩
    by_contra hlt
    push Not at hlt
    have h1 : p ∣ n.factorial := Nat.dvd_factorial hp.pos hlt.le
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hpd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

end H029

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Euclid: a prime factor `p` of `n! + 1` satisfies `n ≤ p`, because `p < n` would make `p` divide
    both `n!` and `n! + 1`, hence `1`. The milestone (a prime factor of every `n ≥ 2`) is strong
    induction: a non-prime `n ≥ 2` has a divisor `m` with `2 ≤ m < n`, and a prime factor of `m`
    divides `n`.
H2. Milestone: `induction n using Nat.strong_induction_on with | _ n ih => …`, then
    `by_cases hp : n.Prime`. Not prime: `Nat.prime_def` and `push Not` give `m ∣ n`, `m ≠ 1`, `m ≠ n`;
    show `m ≠ 0` and `m < n` (`Nat.le_of_dvd`, `Nat.lt_of_le_of_ne`), apply `ih m`, finish with `dvd_trans`.
    Main: the milestone at `n.factorial + 1`, `refine ⟨p, ?_, hp⟩`, `by_contra hlt`, `push Not at hlt`.
H3. `obtain ⟨m, hmn, hm1, hmn'⟩ : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by rw [Nat.prime_def] at hp; push Not at hp; exact hp hn`;
    `Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hmn) hmn'`. Main: `Nat.dvd_factorial hp.pos hlt.le : p ∣ n.factorial`,
    `(Nat.dvd_add_right h1).mp hpd : p ∣ 1`, and `hp.one_lt.ne' (Nat.dvd_one.mp h2) : False`.
-/

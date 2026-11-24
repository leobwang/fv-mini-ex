/- E043 | Primes by norm_num | 2 min | Nat.Prime, norm_num, mathlib
GOAL
  Decide primality of concrete numbers with `norm_num`, and prove facts about a symbolic prime `p`
  (`hp : Nat.Prime p`) with library lemmas called by dot notation on `hp`.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · prime_97
  1. `97` is a numeral: let the primality check decide it.                      R1
-/
-- BEGIN SPEC
theorem prime_97 : Nat.Prime 97 :=
-- END SPEC
  sorry

/- SKELETON · not_prime_91
  1. `91` is a numeral: the same check finds a factor.                           R2
-/
-- BEGIN SPEC
theorem not_prime_91 : ¬ Nat.Prime 91 :=
-- END SPEC
  sorry

/- SKELETON · prime_ge_two
  1. `p` is a variable, so nothing to compute: the goal is one library lemma
     applied to `hp` by dot notation (term mode or `exact`).                      R3
-/
-- BEGIN SPEC
theorem prime_ge_two (p : ℕ) (hp : p.Prime) : 2 ≤ p :=
-- END SPEC
  sorry

/- SKELETON · prime_odd
  1. One library lemma on `hp`; its second argument is `h : p ≠ 2`.              R4
-/
-- BEGIN SPEC
theorem prime_odd (p : ℕ) (hp : p.Prime) (h : p ≠ 2) : Odd p :=
-- END SPEC
  sorry

/- SKELETON · three_dvd_prime
  1. A divisor of a prime is 1 or the prime: get `3 = 1 ∨ 3 = p` from `hp`, `h`
     and split it at once (`rcases` takes the lemma term directly).              R5 → R6
  2. Branch `3 = 1`: a false numeral equation closes the goal.                   R7
  3. Branch `3 = p`: the goal `p = 3` turned around.                             R7
-/
-- BEGIN SPEC
theorem three_dvd_prime (p : ℕ) (hp : p.Prime) (h : 3 ∣ p) : p = 3 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Concrete numerals (`97`, `91`): `norm_num` decides primality. A variable `p`: use what `hp` gives you,
    through lemmas in the namespace `Nat.Prime` (dot notation `hp.lemma`).
H2. `prime_ge_two` and `prime_odd` are each one lemma: `Nat.Prime.two_le`, `Nat.Prime.odd_of_ne_two`.
    `three_dvd_prime`: a divisor of a prime is `1` or the prime itself (`Nat.Prime.eq_one_or_self_of_dvd`);
    split that disjunction and finish both branches with arithmetic.
H3. `prime_ge_two`: `hp.two_le`. `prime_odd`: `hp.odd_of_ne_two h`.
    `three_dvd_prime`: `rcases hp.eq_one_or_self_of_dvd 3 h with h3 | h3` then `omega` in both cases.
-/

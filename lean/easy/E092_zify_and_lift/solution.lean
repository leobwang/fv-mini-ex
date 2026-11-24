/- E092 | zify and lift | 3-5 min | zify, lift, norm_cast, Nat subtraction, mathlib
GOAL
  `zify_ex`: prove an identity with truncated `ℕ` subtraction by moving it to `ℤ`.
  `lift_dvd`: turn a nonnegative integer into a natural number, to use an `ℕ`-only lemma.

BANNED: grind, nlinarith, linarith, polyrith, interval_cases, Nat.sub_one_mul, exact?, try?

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E092

/- SKELETON · zify_ex
  1. Two truncated subtractions, `n - 1` and `n ^ 2 - 1`; `h` covers the first.
     Prove the fact for the second, `h2 : 1 ≤ n ^ 2`, in a `have`:                R1
  2. Move the goal to ℤ, giving `zify` both facts `h` and `h2`:                 R2
  3. What is left is ring algebra in the unknown `↑n`:                          R3
-/
-- BEGIN SPEC
theorem zify_ex (n : ℕ) (h : 1 ≤ n) : (n - 1) * (n + 1) = n ^ 2 - 1 :=
-- END SPEC
  by
    have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ h
    zify [h, h2]
    ring

/- SKELETON · lift_dvd
  1. Replace `x : ℤ` by a natural number, using `hx`:                            R4
  2. Strip the casts from `h`, `h1` and the goal:                                R5
  3. Turn `h : x ∣ 7` into `x = 1 ∨ x = 7`; the primality side goal by R7:       R6, R7
  4. Rule out `x = 1` with `h1` and close the goal:                              R8
-/
-- BEGIN SPEC
theorem lift_dvd (x : ℤ) (hx : 0 ≤ x) (h : x ∣ 7) (h1 : x ≠ 1) : x = 7 :=
-- END SPEC
  by
    lift x to ℕ using hx
    norm_cast at h h1 ⊢
    exact ((Nat.dvd_prime (by norm_num)).mp h).resolve_left h1

end E092

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `zify_ex` has two subtractions, `n - 1` and `n ^ 2 - 1`; `zify` removes the cast of `a - b` only
    when it is given `b ≤ a`. In `lift_dvd`, `Nat.dvd_prime` speaks about `ℕ`, while `x : ℤ`; `hx`
    says `x` is really a natural number.
H2. `zify_ex`: prove `1 ≤ n ^ 2` first (`Nat.one_le_pow`), then `zify` with both facts and finish with
    `ring`. `lift_dvd`: `lift x to ℕ using hx`, then `norm_cast at h h1 ⊢` turns everything into `ℕ`
    statements; `Nat.dvd_prime` gives `x = 1 ∨ x = 7`, and `h1` excludes the left case.
H3. `have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ h; zify [h, h2]; ring`;
    `exact ((Nat.dvd_prime (by norm_num)).mp h).resolve_left h1`.
-/

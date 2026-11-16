/- E092 | zify and lift | 3-5 min | zify, lift, norm_cast, Nat subtraction, mathlib
GOAL
  `zify_ex`: prove an identity with truncated `ℕ` subtraction by moving it to `ℤ`.
  `lift_dvd`: turn a nonnegative integer into a natural number, to use an `ℕ`-only lemma.

REFERENCE
  example (a b : ℕ) (h : b ≤ a) : a - b + b = a := by zify [h]; ring  -- goal moves to ℤ
  -- `↑a` is the cast of `a : ℕ` into ℤ; `zify [h]` turns `↑(a - b)` into `↑a - ↑b`
  #check Nat.one_le_pow   -- (n m : ℕ) : 0 < m → 1 ≤ m ^ n
  example (x : ℤ) (hx : 0 ≤ x) (h : x < 2) : x ≤ 1 := by
    lift x to ℕ using hx; omega    -- now x : ℕ, and h : (x : ℤ) < 2
  example (x : ℕ) (h : (x : ℤ) ∣ 7) : x ∣ 7 := by norm_cast at h   -- strip casts in h
  #check Nat.dvd_prime    -- p.Prime → (m ∣ p ↔ m = 1 ∨ m = p)
  example : Nat.Prime 7 := by norm_num   -- closes primality side goals for literals
  example (A B : Prop) (h : A ∨ B) (hne : ¬A) : B := h.resolve_left hne
BANNED: grind, nlinarith, linarith, polyrith, interval_cases, Nat.sub_one_mul, exact?, try?
NOTE: in ℕ, `a - b = 0` when `b > a`; `zify [h₁, h₂]` needs every `b ≤ a` that makes a `-` exact.
-/
import Mathlib

namespace E092

-- BEGIN SPEC
theorem zify_ex (n : ℕ) (h : 1 ≤ n) : (n - 1) * (n + 1) = n ^ 2 - 1 :=
-- END SPEC
  by
    have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ h
    zify [h, h2]
    ring

-- BEGIN SPEC
theorem lift_dvd (x : ℤ) (hx : 0 ≤ x) (h : x ∣ 7) (h1 : x ≠ 1) : x = 7 :=
-- END SPEC
  by
    lift x to ℕ using hx
    norm_cast at h h1 ⊢
    exact ((Nat.dvd_prime (by norm_num)).mp h).resolve_left h1

end E092

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `zify_ex` has two subtractions, `n - 1` and `n ^ 2 - 1`; each needs its `1 ≤ _` fact for
    `zify`. In `lift_dvd`, `Nat.dvd_prime` speaks about `ℕ`, while `x : ℤ`.
H2. Prove `1 ≤ n ^ 2` first, then `zify` with both facts and finish with `ring`. For `lift_dvd`,
    `lift x to ℕ using hx`, then `norm_cast at h h1 ⊢` turns everything into `ℕ` statements.
H3. `have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ h; zify [h, h2]; ring`;
    `exact ((Nat.dvd_prime (by norm_num)).mp h).resolve_left h1`.
-/

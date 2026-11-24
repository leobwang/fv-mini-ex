/- M061 | Chinese remainder theorem | 15 min | Int.ModEq, IsCoprime, divisibility witnesses, linear_combination, mathlib
GOAL
  For coprime integers `m, n`, find `x` with `x ≡ a (mod m)` and `x ≡ b (mod n)`, and show any two
  solutions agree mod `m * n`. Over ℤ, `IsCoprime m n` means Bézout: `∃ u v, u * m + v * n = 1`.
BANNED: Int.modEq_and_modEq_iff_modEq_mul, Nat.modEq_and_modEq_iff_modEq_mul, Nat.chineseRemainder, Nat.chineseRemainder', ZMod.chineseRemainder, IsCoprime.mul_dvd, Nat.Coprime.mul_dvd_of_dvd_of_dvd, exact?, apply?, rw?, hint, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M061

/- SKELETON · crt_exists
  1. Unpack Bézout: context gains `u v` and `huv : u * m + v * n = 1`:        R1
  2. Choose x₀ = a·(v·n) + b·(u·m) (since v·n ≡ 1 mod m, u·m ≡ 1 mod n) and
     split into the two congruences:                                       R2
  3. On both goals (`<;>`): congruence → divisibility; the goals become
     `m ∣ a - x₀` and `n ∣ b - x₀` (right side minus left side):            R3
  4. In each goal: give the quotient (a multiple of `u` for `m`, of `v` for
     `n`), then close the equation with one multiple of `huv`:              R4 → R5
-/
-- BEGIN SPEC
theorem crt_exists (m n : ℤ) (h : IsCoprime m n) (a b : ℤ) :
    ∃ x, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] :=
-- END SPEC
  by
    obtain ⟨u, v, huv⟩ := h
    refine ⟨a * v * n + b * u * m, ?_, ?_⟩ <;> rw [Int.modEq_iff_dvd]
    · exact ⟨a * u - b * u, by linear_combination (-a) * huv⟩
    · exact ⟨b * v - a * v, by linear_combination (-b) * huv⟩

/- SKELETON · crt_unique
  1. Unpack Bézout:                                                         R1
  2. All three congruences → divisibilities of `y - x` at once:             R6
  3. Unpack `hm`, `hn`: `hs : y - x = m * s`, `ht : y - x = n * t`:         R7, R7
  4. Witness for `m * n ∣ y - x`: write y - x = u·m·(y - x) + v·n·(y - x),
     replace `y - x` by `n * t` in the first term, by `m * s` in the second: R4
  5. Close the equation from `huv`, `hs`, `ht` (three coefficients):        R5
-/
-- BEGIN SPEC
theorem crt_unique (m n : ℤ) (h : IsCoprime m n) (x y : ℤ)
    (hm : x ≡ y [ZMOD m]) (hn : x ≡ y [ZMOD n]) : x ≡ y [ZMOD m * n] :=
-- END SPEC
  by
    obtain ⟨u, v, huv⟩ := h
    rw [Int.modEq_iff_dvd] at *
    obtain ⟨s, hs⟩ := hm
    obtain ⟨t, ht⟩ := hn
    -- WHY: y - x = (y - x) * (u * m + v * n) = m * n * (u * t) + m * n * (v * s)
    exact ⟨u * t + v * s, by linear_combination (-(y - x)) * huv + u * m * ht + v * n * hs⟩

end M061

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `v * n ≡ 1 (mod m)` and `u * m ≡ 1 (mod n)`, so `x = a * (v * n) + b * (u * m)` works.
    After `rw [Int.modEq_iff_dvd]` every congruence is a divisibility; give explicit witnesses.
H2. Existence: `m ∣ a - x` with witness `a * u - b * u`, and symmetrically for `n`. Uniqueness: from
    `y - x = m * s` and `y - x = n * t`, multiply `u * m + v * n = 1` by `y - x`.
H3. `refine ⟨a * v * n + b * u * m, ?_, ?_⟩ <;> rw [Int.modEq_iff_dvd]`, then
    `exact ⟨a * u - b * u, by linear_combination c * huv⟩` for the right coefficient `c` (a multiple of `a`).
    Uniqueness: witness `u * t + v * s`, closed by `linear_combination e * huv + u * m * ht + v * n * hs`
    for the right `e` (a multiple of `y - x`).
-/

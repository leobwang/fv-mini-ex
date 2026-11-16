/- M061 | Chinese remainder theorem | 15 min | Int.ModEq, IsCoprime, divisibility witnesses, linear_combination, mathlib
GOAL
  For coprime integers `m, n`, find `x` with `x ≡ a (mod m)` and `x ≡ b (mod n)`, and show any two
  solutions agree mod `m * n`. Over ℤ, `IsCoprime m n` means Bézout: `∃ u v, u * m + v * n = 1`.

REFERENCE
  #check Int.modEq_iff_dvd   -- a ≡ b [ZMOD n] ↔ n ∣ b - a      (`[ZMOD n]` is `Int.ModEq n`)
  example (m n : ℤ) (h : IsCoprime m n) : ∃ u v, u * m + v * n = 1 := h   -- unfolds by definition
  example (a b c : ℤ) (h : a = b * c) : b ∣ a := ⟨c, h⟩   -- `b ∣ a` is `∃ c, a = b * c`
  example (x u v m n : ℤ) (huv : u * m + v * n = 1) : x * u * m + x * v * n = x := by
    linear_combination x * huv   -- goal = (coefficients) * hypotheses, checked by `ring`
  -- `obtain ⟨u, v, huv⟩ := h` unpacks Bézout; `obtain ⟨s, hs⟩ := hdvd` unpacks `m ∣ _`.
BANNED: Int.modEq_and_modEq_iff_modEq_mul, Nat.modEq_and_modEq_iff_modEq_mul, Nat.chineseRemainder, Nat.chineseRemainder', ZMod.chineseRemainder, IsCoprime.mul_dvd, Nat.Coprime.mul_dvd_of_dvd_of_dvd, exact?, apply?, rw?, hint, try?
NOTE: search tactics (`exact?`, `try?`, ...) are fine for exploring, but they close goals with banned lemmas, so they cannot stay.
-/
import Mathlib

namespace M061

-- BEGIN SPEC
theorem crt_exists (m n : ℤ) (h : IsCoprime m n) (a b : ℤ) :
    ∃ x, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] :=
-- END SPEC
  by
    obtain ⟨u, v, huv⟩ := h
    refine ⟨a * v * n + b * u * m, ?_, ?_⟩ <;> rw [Int.modEq_iff_dvd]
    · exact ⟨a * u - b * u, by linear_combination (-a) * huv⟩
    · exact ⟨b * v - a * v, by linear_combination (-b) * huv⟩

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
    `exact ⟨a * u - b * u, by linear_combination c * huv⟩` for the right coefficient `c`.
    Uniqueness: witness `u * t + v * s`, closed by `linear_combination` from `huv`, `hs`, `ht`.
-/

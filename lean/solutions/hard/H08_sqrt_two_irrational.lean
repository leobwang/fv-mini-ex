/- H08 | √2 is irrational | 1-1.5 h | infinite descent, parity, casts, Irrational, mathlib
GOAL
  Prove `p² ≠ 2q²` for natural `q > 0` by infinite descent, then transfer it to the reals:
  `√2` is irrational.

REFERENCE
  #check Nat.Prime.dvd_of_dvd_pow   -- p.Prime → p ∣ m ^ n → p ∣ m   (use with Nat.prime_two)
  #check irrational_iff_ne_rational -- Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b
  #check Real.sq_sqrt               -- 0 ≤ a → √a ^ 2 = a
  #check Int.natAbs_pow             -- (n ^ k).natAbs = n.natAbs ^ k
  example (a b : ℤ) (h : (a : ℝ) = b) : a = b := by exact_mod_cast h   -- casts back down
  -- Descent: `induction q using Nat.strong_induction_on generalizing p`.
BANNED: irrational_sqrt_two, Nat.Prime.irrational_sqrt, irrational_sqrt_natCast_iff, irrational_nrt_of_notint_nrt, irrational_sqrt_of_multiplicity_odd, irrational_sqrt_ratCast_iff, Irrational.of_pow, irrational_sqrt_intCast_iff
-/
import Mathlib

namespace H08

-- BEGIN SPEC
theorem sq_ne_two_mul_sq (p q : ℕ) (hq : 0 < q) : p ^ 2 ≠ 2 * q ^ 2 :=
-- END SPEC
  by
    induction q using Nat.strong_induction_on generalizing p with
    | _ q ih =>
      intro h
      obtain ⟨k, rfl⟩ : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ p ^ 2 from ⟨q ^ 2, h⟩)
      have hq2 : q ^ 2 = 2 * k ^ 2 := by linarith
      obtain ⟨m, rfl⟩ : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ q ^ 2 from ⟨k ^ 2, hq2⟩)
      exact ih m (by omega) k (by omega) (by linarith)

-- BEGIN SPEC
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
-- END SPEC
  by
    rw [irrational_iff_ne_rational]
    intro a b hb0 h
    have hb : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
    have h2 : (a : ℝ) ^ 2 = 2 * (b : ℝ) ^ 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      rw [h, div_pow] at this
      field_simp at this
      linarith
    have h3 : a ^ 2 = 2 * b ^ 2 := by exact_mod_cast h2
    have h4 : a.natAbs ^ 2 = 2 * b.natAbs ^ 2 := by
      have := congrArg Int.natAbs h3
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    exact sq_ne_two_mul_sq _ _ (Int.natAbs_pos.mpr hb0) h4

end H08

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. If `p² = 2q²` then `p` is even, `p = 2k`, so `q² = 2k²`, so `q = 2m` is even and `k² = 2m²` with `m < q`: descend.
H2. Real part: from `√2 = a / b` get `a² = 2 b²` over ℝ (square both sides, clear the denominator), cast it to ℤ, then take `natAbs` to land in ℕ.
H3. Descent step: `obtain ⟨k, rfl⟩ : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow ⟨q ^ 2, h⟩`, the same for `q`, then `exact ih m (by omega) k (by omega) (by linarith)`.
-/

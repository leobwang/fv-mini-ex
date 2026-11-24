/- M178 | Lorentz matrices have determinant ±1 | 10-15 min | Matrix.det, det_mul, det_transpose, mul_self_eq_one_iff, physlib
GOAL
  A Lorentz matrix `Λ` satisfies `Λᵀ η Λ = η` (`η = diag(1, -1, …, -1)`, the Minkowski metric).
  Deduce `det Λ = 1 ∨ det Λ = -1`.
BANNED: LorentzGroup.det_eq_one_or_neg_one

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.LorentzGroup.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace M178

/- SKELETON · det_pm_one   (write `det Λ` for `Λ.1.det`, printed `(↑Λ).det`)
  1. Determinants of both sides of `Λᵀ * η * Λ = η`, as a hypothesis h:      R1 inside R2
  2. Evaluate them in ONE `simp only [...] at h`:                            R3, R4, R5
       h : det Λ * (-1) ^ d * det Λ = (-1) ^ d
  3. The factored form (type the scalar: `((-1 : ℝ) ^ d)`):                  R6
       h0 : (-1) ^ d * (det Λ * det Λ - 1) = 0
  4. The factor is nonzero:                                                  R7 with R8
       hd : (-1) ^ d ≠ 0
  5. h1 : det Λ * det Λ = 1: zero product, drop the `(-1) ^ d = 0` side,
     then move the `- 1`:                                                    R9 → R10, R11
  6. The square → the two values:                                            R12
-/
-- BEGIN SPEC
theorem det_pm_one {d : ℕ} (Λ : LorentzGroup d) : Λ.1.det = 1 ∨ Λ.1.det = -1 :=
-- END SPEC
  sorry

end M178

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Take determinants of both sides of `Λᵀ η Λ = η`; you get `det Λ * (-1) ^ d * det Λ = (-1) ^ d`.
    Since `(-1) ^ d ≠ 0`, `det Λ * det Λ = 1`, and a number whose square is `1` is `±1`.
H2. Cancel `(-1) ^ d` through a zero product: `(-1) ^ d * (det Λ * det Λ - 1) = 0` (R6), the first
    factor is nonzero (R7, R8), so the second is zero (R9, R10). Finish with R11, then R12.
H3. `have h := congrArg Matrix.det (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ))`,
    `simp only [det_mul, det_transpose, det_eq_neg_one_pow_d] at h`,
    `have h0 : ((-1 : ℝ) ^ d) * (Λ.1.det * Λ.1.det - 1) = 0 := by linear_combination h`,
    `have hd : ((-1 : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by norm_num)`, then
    `(mul_eq_zero.mp h0).resolve_left hd`, `linarith`, and `exact mul_self_eq_one_iff.mp h1`.
-/

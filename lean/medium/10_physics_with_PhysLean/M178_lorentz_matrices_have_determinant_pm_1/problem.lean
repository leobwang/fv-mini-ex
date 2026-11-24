/- M178 | Lorentz matrices have determinant ±1 | 10-15 min | Matrix.det, det_mul, det_transpose, mul_self_eq_one_iff, physlib
GOAL
  A Lorentz matrix `Λ` satisfies `Λᵀ η Λ = η` (`η = diag(1, -1, …, -1)`, the Minkowski metric).
  Deduce `det Λ = 1 ∨ det Λ = -1`.

REFERENCE
  -- `Λ : LorentzGroup d` is a subtype of matrices over `Fin 1 ⊕ Fin d`; `Λ.1` is the matrix itself
  example (d : ℕ) (Λ : LorentzGroup d) : Λ.1.transpose * minkowskiMatrix * Λ.1 = minkowskiMatrix :=
    LorentzGroup.transpose_mul_minkowskiMatrix_mul_self   -- `Λ` is implicit: pass `(Λ := Λ)` in a `have`
  #check Matrix.det_mul       -- (M * N).det = M.det * N.det
  #check Matrix.det_transpose -- Mᵀ.det = M.det
  #check minkowskiMatrix.det_eq_neg_one_pow_d   -- η.det = (-1) ^ d
  #check mul_self_eq_one_iff  -- a * a = 1 ↔ a = 1 ∨ a = -1
  example (M N : Matrix (Fin 2) (Fin 2) ℝ) (h : M = N) : M.det = N.det := congrArg Matrix.det h
  -- `linear_combination e * h` proves an equation that is `e` times the equation `h`, up to `ring`
BANNED: LorentzGroup.det_eq_one_or_neg_one
-/
import Physlib.Relativity.LorentzGroup.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace M178

-- BEGIN SPEC
theorem det_pm_one {d : ℕ} (Λ : LorentzGroup d) : Λ.1.det = 1 ∨ Λ.1.det = -1 :=
-- END SPEC
  sorry

end M178

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Take determinants of both sides of `Λᵀ η Λ = η`.
H2. That gives `det Λ * (-1) ^ d * det Λ = (-1) ^ d`; since `(-1) ^ d ≠ 0`, `det Λ * det Λ = 1`.
H3. `have h := congrArg Matrix.det (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ))`,
    `simp only [det_mul, det_transpose, det_eq_neg_one_pow_d] at h`, then cancel `(-1) ^ d` via
    `(-1) ^ d * (det Λ * det Λ - 1) = 0` and `mul_eq_zero`, and finish with `mul_self_eq_one_iff.mp`.
-/

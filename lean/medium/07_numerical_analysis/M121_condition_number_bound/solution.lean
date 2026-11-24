/- M121 | Condition number bound | 10-15 min | Matrix norms, mulVec, operator norm, relative error, mathlib
GOAL
  If `A x = b`, `A x' = b'` and `B A = 1`, the relative error in the solution is at most
  `κ = ‖A‖ ‖B‖` (the condition number) times the relative error in the data, in the ∞-norm.

REFERENCE
  open Matrix                            -- for `A *ᵥ v` (matrix times vector)
  open scoped Matrix.Norms.Operator      -- makes `‖A‖` the ∞-operator norm (max row sum of `|A i j|`)
  #check Matrix.linfty_opNorm_mulVec     -- ‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖
  #check Matrix.mulVec_sub               -- A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y
  #check Matrix.mulVec_mulVec            -- M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v
  #check Matrix.one_mulVec               -- 1 *ᵥ v = v        (and `Matrix.mulVec_zero : A *ᵥ 0 = 0`)
  #check norm_pos_iff                    -- 0 < ‖a‖ ↔ a ≠ 0
  #check div_le_iff₀                     -- 0 < c → (b / c ≤ a ↔ b ≤ a * c)
  example (a b c : ℝ) (hc : 0 ≤ c) (h : a ≤ b) : c * a ≤ c * b := by gcongr
  `‖v‖` for `v : Fin n → ℝ` is the sup norm `max i |v i|`.
-/
import Mathlib

namespace M121
open Matrix
open scoped Matrix.Norms.Operator

-- BEGIN SPEC
theorem relative_error_le_cond {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hBA : B * A = 1)
    (x x' b b' : Fin n → ℝ) (hx : A *ᵥ x = b) (hx' : A *ᵥ x' = b') (hb : b ≠ 0) :
    ‖x' - x‖ / ‖x‖ ≤ ‖A‖ * ‖B‖ * (‖b' - b‖ / ‖b‖) :=
-- END SPEC
  by
    have hdx : x' - x = B *ᵥ (b' - b) := by
      rw [← hx, ← hx', ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    have hxne : x ≠ 0 := by
      rintro rfl
      exact hb (by rw [← hx, Matrix.mulVec_zero])
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have h1 : ‖x' - x‖ ≤ ‖B‖ * ‖b' - b‖ := hdx ▸ Matrix.linfty_opNorm_mulVec _ _
    have h2 : ‖b‖ ≤ ‖A‖ * ‖x‖ := hx ▸ Matrix.linfty_opNorm_mulVec _ _
    rw [div_le_iff₀ hxpos]
    calc ‖x' - x‖ ≤ ‖B‖ * ‖b' - b‖ := h1
      _ = ‖B‖ * (‖b' - b‖ / ‖b‖) * ‖b‖ := by field_simp
      _ ≤ ‖B‖ * (‖b' - b‖ / ‖b‖) * (‖A‖ * ‖x‖) := by gcongr
      _ = ‖A‖ * ‖B‖ * (‖b' - b‖ / ‖b‖) * ‖x‖ := by ring

end M121

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two one-line bounds do all the work: one on the error `x' - x` via `B`, one on `‖b‖` via `A`.
H2. Show `x' - x = B *ᵥ (b' - b)` by rewriting with `hx`, `hx'` backwards; show `x ≠ 0` (else `b = A *ᵥ 0 = 0`); then clear the denominator `‖x‖`.
H3. `‖x' - x‖ ≤ ‖B‖ * ‖b' - b‖` and `‖b‖ ≤ ‖A‖ * ‖x‖` (both `linfty_opNorm_mulVec`); after `rw [div_le_iff₀ hxpos]`, `calc` through `‖B‖ * (‖b' - b‖ / ‖b‖) * ‖b‖` (by `field_simp`) and `gcongr`.
-/

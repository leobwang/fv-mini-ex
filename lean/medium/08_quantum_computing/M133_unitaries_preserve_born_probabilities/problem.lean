/- M133 | Unitaries preserve Born probabilities | 15-20 min | Ket, unitaryGroup, star_mulVec, dotProduct, physlib
GOAL
  For a unitary `U` and a normalised ket `ψ`, the Born probabilities `|(Uψ)ᵢ|²` of measuring `Uψ`
  in the computational basis still sum to 1.

REFERENCE
  -- context for the examples: `variable {d : Type} [Fintype d] [DecidableEq d]`
  example (U : 𝐔[d]) : Matrix d d ℂ := U.val         -- `𝐔[d]` = `Matrix.unitaryGroup d ℂ`
  example (ψ : Ket d) : ∑ i, ‖ψ.vec i‖ ^ 2 = 1 := ψ.normalized'   -- `ψ.vec : d → ℂ`
  example (v w : d → ℂ) : star v ⬝ᵥ w = ∑ i, star (v i) * w i := rfl   -- `⬝ᵥ` dot product
  #check Matrix.star_mulVec     -- star (M *ᵥ v) = star v ᵥ* Mᴴ   (`*ᵥ` matrix·vector, `ᵥ*` vector·matrix)
  #check Matrix.dotProduct_mulVec   -- v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w
  #check Matrix.vecMul_vecMul   -- v ᵥ* M ᵥ* N = v ᵥ* (M * N)
  #check Matrix.vecMul_one      -- v ᵥ* 1 = v
  #check Matrix.star_eq_conjTranspose   -- star M = Mᴴ
  #check Matrix.UnitaryGroup.star_mul_self   -- star ↑U * ↑U = 1
  #check Complex.conj_mul'      -- conj z * z = ‖z‖ ^ 2   (`starRingEnd ℂ` = conj = `star` on ℂ)
  example (x : ℝ) (h : (x : ℂ) = 1) : x = 1 := by exact_mod_cast h   -- move casts ℝ ↔ ℂ
-/
import QuantumInfo.Operators.Unitary

open scoped Matrix

namespace M133

-- BEGIN SPEC
theorem unitary_born {d : Type} [Fintype d] [DecidableEq d] (U : 𝐔[d]) (ψ : Ket d) :
    ∑ i, ‖(U.val *ᵥ ψ.vec) i‖ ^ 2 = 1 :=
-- END SPEC
  sorry

end M133

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The sum `∑ ‖vᵢ‖²` is the real version of the complex number `star v ⬝ᵥ v`. Prove that
    `U` does not change `star v ⬝ᵥ v`, then transfer back to `ℝ` and use `ψ.normalized'`.
H2. Two `have`s: (a) `star (U.val *ᵥ v) ⬝ᵥ (U.val *ᵥ v) = star v ⬝ᵥ v` by a `rw` chain through the
    REFERENCE lemmas; (b) `∀ v : d → ℂ, ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v`.
H3. (a): `rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.vecMul_one]`;
    (b): `intro v; simp [dotProduct, Complex.conj_mul']`. Then chain them, `rw [ψ.normalized'] at h`,
    and `exact_mod_cast h`.
-/

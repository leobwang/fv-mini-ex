/- M181 | The magnetic force does no work | 5-10 min | EuclideanSpace inner product, cross product, PiLp.inner_apply, physlib
GOAL
  A charge `q` moving with velocity `v` in fields `E`, `B` feels the Lorentz force `F = q (E + v × B)`.
  Show that the power `v · F` equals `q (v · E)`: the magnetic part `v × B` is orthogonal to `v`.

REFERENCE
  `EuclideanSpace ℝ (Fin 3)` is ℝ³ with its dot product `⟪x, y⟫_ℝ` (needs `open InnerProductSpace`).
  `a ⨯ₑ₃ b` is physlib's cross product on it (Mathlib's `⨯₃` on `Fin 3 → ℝ`; needs `open Matrix`).
  #check real_inner_smul_right  -- ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ
  #check inner_add_right        -- ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
  #check PiLp.inner_apply       -- ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫   (the dot product, componentwise)
  #check Fin.sum_univ_three     -- ∑ i, f i = f 0 + f 1 + f 2
  #check cross_apply            -- a ⨯₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  example (a b : EuclideanSpace ℝ (Fin 3)) : (a ⨯ₑ₃ b) 0 = a 1 * b 2 - a 2 * b 1 := by simp [cross_apply]
BANNED: inner_self_cross, inner_cross_self, dot_self_cross, dot_cross_self, exact?, apply?, rw?, hint, observe, try?
-/
import Physlib.SpaceAndTime.Space.CrossProduct

open Space InnerProductSpace Matrix

namespace M181

-- BEGIN SPEC
/-- The Lorentz force on a charge `q` with velocity `v` in fields `E` and `B`. -/
noncomputable def lorentzForce (q : ℝ) (E B v : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  q • (E + v ⨯ₑ₃ B)
-- END SPEC

-- BEGIN SPEC
theorem lorentzForce_power (q : ℝ) (E B v : EuclideanSpace ℝ (Fin 3)) :
    ⟪v, lorentzForce q E B v⟫_ℝ = q * ⟪v, E⟫_ℝ :=
-- END SPEC
  sorry

end M181

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `lorentzForce` and pull `q` and the sum out of the inner product; what is left is `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0`.
H2. Prove `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0` by components: the inner product is a sum over `Fin 3`, each component of
    the cross product is given by `cross_apply`, and the six products cancel in pairs (`ring`).
H3. The key line is `have h : ⟪v, v ⨯ₑ₃ B⟫_ℝ = 0`, proved by `simp only [PiLp.inner_apply]`, then `simp` with
    `Fin.sum_univ_three` and `cross_apply`, then `ring`.
-/

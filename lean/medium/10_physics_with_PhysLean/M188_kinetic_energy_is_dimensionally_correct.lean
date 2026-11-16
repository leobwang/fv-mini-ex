/- M188 | Kinetic energy is dimensionally correct | 15 min | WithDim, scaleUnit, dimScale, field_simp, physlib
GOAL
  The relation `E = ½ m v²`, stated on the raw numbers of a mass, a velocity and an energy, holds in one
  system of units iff it holds in every other. Unlike E125 the types do not check this: track the scale factors.

REFERENCE
  `WithDim d ℝ`: a real number tagged with dimension `d` (`M𝓭 L𝓭 T𝓭` = mass, length, time); `x.1 = x.val`.
  `scaleUnit u1 u2 x` converts `x` from unit system `u1` to `u2`; `u1.dimScale u2 d : NNReal` is the factor.
  #check isDimensionallyCorrect_fun_iff -- IsDimensionallyCorrect f ↔ ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m
  #check WithDim.scaleUnit_val          -- (scaleUnit u1 u2 m).val = (u1.dimScale u2) d • m.val
  #check LTMCTUnitChoices.dimScale_pos  -- 0 < (u1.dimScale u2) d
  #check NNReal.smul_def                -- c • x = (c : ℝ) • x   for `c : NNReal`
  #check NNReal.coe_mul                 -- ((r₁ * r₂ : NNReal) : ℝ) = r₁ * r₂   (also `NNReal.coe_inv`)
  `map_mul`, `map_inv`: `u1.dimScale u2` is a monoid hom, so it splits over `M𝓭 * L𝓭 * T𝓭⁻¹ * ...`.
  `simp [funext_iff, KineticEnergy]` turns the goal into `∀ u1 u2 m v E, (rescaled equation ↔ equation)`.
  `field_simp` clears nonzero denominators (give it `hT : x ≠ 0` facts); `linear_combination h / 2` finishes.
-/
import Physlib.Units.WithDim.Speed

open Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim WithDim

namespace M188

-- BEGIN SPEC
/-- `E = ½ m v²` on the raw numbers. -/
def KineticEnergy (m : WithDim M𝓭 ℝ) (v : WithDim (L𝓭 * T𝓭⁻¹) ℝ)
    (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) : Prop :=
  E.1 = 1/2 * m.1 * v.1 ^ 2
-- END SPEC

-- BEGIN SPEC
theorem kineticEnergy_isDimensionallyCorrect : IsDimensionallyCorrect KineticEnergy :=
-- END SPEC
  sorry

end M188

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. After pushing `scaleUnit` onto the arguments, every side carries scale factors `s_M`, `s_L`, `s_T`
    (one per base dimension, all positive). The rescaled equation is the original one times
    `s_M s_L² / s_T²` on both sides.
H2. `simp [funext_iff, KineticEnergy]; intro u1 u2 m v E`, then split every `dimScale` of a product with
    `simp only [WithDim.scaleUnit_val, WithDim.withDim_hMul_val, map_mul, map_inv, NNReal.smul_def,
    smul_eq_mul, NNReal.coe_mul, NNReal.coe_inv]`. Record `(dimScale_pos u2 u1 M𝓭).ne'` and the same for
    `L𝓭`, `T𝓭`.
H3. `constructor <;> intro h`; forward: `field_simp at h; linear_combination h / 2`;
    backward: `rw [h]; field_simp`.
-/

/- M188 | Kinetic energy is dimensionally correct | 15 min | WithDim, scaleUnit, dimScale, field_simp, physlib
GOAL
  The relation `E = ½ m v²`, stated on the raw numbers of a mass, a velocity and an energy, holds in one
  system of units iff it holds in every other. Unlike E125 the types do not check this: track the scale factors.

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · kineticEnergy_isDimensionallyCorrect
  1. Definition → `∀ u1 u2 m v E, (rescaled relation ↔ relation)`:
       `simp` with `funext_iff` and `KineticEnergy`                          R1 → R2 → R3 → R2 → R4 → R5
       (it also rewrites `1/2` as `2⁻¹` and `v.1 ^ 2` as `(v * v).val`)     R6, R7, R8
  2. Name the quantities: `intro u1 u2 m v E`
  3. One `simp only`: rescaled values → factors × values, every factor
     `(u2.dimScale u1) (product)` split into real casts of the base factors   R9, R10, R11, R12, R13, R14, R15, R16
  4. Three facts `(u2.dimScale u1) X ≠ 0` for X = M𝓭, L𝓭, T𝓭 (order `u2 u1`!) R17 → R18
  5. Split the `↔` and name the assumption `h`                              R19, intro h
  6. mp (rescaled → original): cancel the factors in `h`, then `h` is twice
     the goal                                                               R20 → R21
  7. mpr (original → rescaled): substitute, then cancel                     rw [h] → R22
-/
-- BEGIN SPEC
theorem kineticEnergy_isDimensionallyCorrect : IsDimensionallyCorrect KineticEnergy :=
-- END SPEC
  sorry

end M188

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. After unfolding, both sides of the rescaled equation carry the scale factors `s_X = (u2.dimScale u1) X`
    of the base dimensions X = M𝓭, L𝓭, T𝓭 (all positive): the rescaled relation is the original one with
    both sides multiplied by `s_M s_L² / s_T²`. Make those factors visible, then cancel them.
H2. `simp [funext_iff, KineticEnergy]` and `intro u1 u2 m v E` give a `↔` of two real equations. Turn every
    rescaled value into real factors with one `simp only` over R9–R16, record `s_X ≠ 0` for the three
    bases, then `constructor <;> intro h`: forward `field_simp at h` + `linear_combination`, backward
    `rw [h]` + `field_simp`.
H3. `simp only [WithDim.scaleUnit_val, WithDim.withDim_hMul_val, map_mul, map_inv, NNReal.smul_def,
    smul_eq_mul, NNReal.coe_mul, NNReal.coe_inv]`, then `have hM := (dimScale_pos u2 u1 M𝓭).ne'` (same for
    `L𝓭`, `T𝓭`). Forward: after `field_simp at h`, `h : E.val * 2 = m.val * v.val ^ 2`; close with
    `linear_combination h / 2`.
-/

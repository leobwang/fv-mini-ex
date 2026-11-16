/- E125 | Momentum is dimensionally correct | 2-3 min | WithDim, Dimension, IsDimensionallyCorrect, scaleUnit, physlib
GOAL
  The relation `p = m · v` between a mass, a velocity and a momentum (typed by their dimensions) holds in
  one system of units iff it holds in every other: prove it is dimensionally correct.

REFERENCE
  `WithDim d ℝ` is a real number tagged with dimension `d`; `M𝓭 L𝓭 T𝓭` are mass, length, time.
  `m * v : WithDim (M𝓭 * (L𝓭 * T𝓭⁻¹)) ℝ`; `cast` retypes it to the equal dimension `M𝓭 * L𝓭 * T𝓭⁻¹`.
  `scaleUnit u1 u2 x` rewrites `x` from unit system `u1` to `u2` (`u1 u2 : LTMCTUnitChoices`, e.g. `SI`).
  example (f : WithDim M𝓭 ℝ → Prop) : IsDimensionallyCorrect f ↔ ∀ u1 u2, scaleUnit u1 u2 f = f := Iff.rfl
  #check isDimensionallyCorrect_fun_iff -- IsDimensionallyCorrect f ↔ ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m
  #check UnitDependent.scaleUnit_apply_fun      -- scaleUnit u1 u2 f m1 = scaleUnit u1 u2 (f (scaleUnit u2 u1 m1))
  #check UnitDependent.scaleUnit_apply_fun_left -- scaleUnit u1 u2 f m1 = f (scaleUnit u2 u1 m1)  (codomain not rescaled)
  #check DMul.hMul_scaleUnit       -- scaleUnit u1 u2 m1 * scaleUnit u1 u2 m2 = scaleUnit u1 u2 (m1 * m2)
  #check WithDim.cast_scaleUnit    -- (scaleUnit u1 u2 m).cast h = scaleUnit u1 u2 (m.cast h)
  #check UnitDependent.scaleUnit_injective -- scaleUnit u1 u2 m1 = scaleUnit u1 u2 m2 ↔ m1 = m2
-/
import Physlib.Units.WithDim.Speed

open Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim WithDim

namespace E125

-- BEGIN SPEC
/-- `p = m · v`, as a relation between dimensionful quantities. -/
def MomentumEq (m : WithDim M𝓭 ℝ) (v : WithDim (L𝓭 * T𝓭⁻¹) ℝ)
    (p : WithDim (M𝓭 * L𝓭 * T𝓭⁻¹) ℝ) : Prop :=
  p = cast (m * v)
-- END SPEC

-- BEGIN SPEC
theorem momentum_isDimensionallyCorrect : IsDimensionallyCorrect MomentumEq :=
-- END SPEC
  by
    rw [isDimensionallyCorrect_fun_iff]
    intro u1 u2 m
    funext v p
    -- the inputs are rescaled `u2 → u1`, the `Prop` output is not
    simp only [scaleUnit_apply_fun, scaleUnit_apply_fun_left, MomentumEq]
    -- goal: `scaleUnit u2 u1 p = cast (scaleUnit u2 u1 m * scaleUnit u2 u1 v) ↔ p = cast (m * v)`
    rw [DMul.hMul_scaleUnit, cast_scaleUnit, scaleUnit_injective]

end E125

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `MomentumEq` is a function of three arguments; peel off the first with `isDimensionallyCorrect_fun_iff`
    and the other two with `funext`.
H2. Push every `scaleUnit` onto the arguments (`scaleUnit_apply_fun`, `scaleUnit_apply_fun_left`), unfold
    `MomentumEq`, then move it outward through `*` and `cast` until both sides of `=` are rescaled.
H3. `rw [isDimensionallyCorrect_fun_iff]; intro u1 u2 m; funext v p`,
    `simp only [scaleUnit_apply_fun, scaleUnit_apply_fun_left, MomentumEq]`, then
    `rw [DMul.hMul_scaleUnit, cast_scaleUnit, scaleUnit_injective]`. (`simp [funext_iff, MomentumEq]` also works.)
-/

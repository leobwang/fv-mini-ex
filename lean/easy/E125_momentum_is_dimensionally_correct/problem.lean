/- E125 | Momentum is dimensionally correct | 2-3 min | WithDim, Dimension, IsDimensionallyCorrect, scaleUnit, physlib
GOAL
  The relation `p = m · v` between a mass, a velocity and a momentum (typed by their dimensions) holds in
  one system of units iff it holds in every other: prove it is dimensionally correct.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · momentum_isDimensionallyCorrect
  1. Definition → `∀ u1 u2 m, …`, one equation per mass `m`; name them:   R1, intro u1 u2 m
  2. Both sides are still functions of `v` and `p`: apply them             R2
  3. Push `scaleUnit` onto `v`, then onto `p`, and unfold `MomentumEq`,
     all in one `simp only`:                                               R3 → R4 → R5
       goal: `(scaleUnit u2 u1 p = (scaleUnit u2 u1 m * scaleUnit u2 u1 v).cast _) = (p = (m * v).cast _)`
  4. Move `scaleUnit u2 u1` outward on the left: through `*`, then `cast`    R6 → R7
  5. Cancel it from both sides of the inner `=`; the goal is now `X = X`     R8 → R9
-/
-- BEGIN SPEC
theorem momentum_isDimensionallyCorrect : IsDimensionallyCorrect MomentumEq :=
-- END SPEC
  sorry

end E125

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `MomentumEq` is a function of three inputs. `isDimensionallyCorrect_fun_iff` peels off the first (the
    mass); `funext` applies both sides to the other two. Then the left side is the relation on converted inputs.
H2. Push every `scaleUnit` onto the arguments (`scaleUnit_apply_fun` at `v`, `scaleUnit_apply_fun_left` at
    `p`, whose output is a `Prop`) and unfold `MomentumEq`. Then move `scaleUnit u2 u1` outward through `*`
    and `cast` until both sides of the inner `=` carry it, and cancel it: converting is injective.
H3. After `funext v p`: `simp only [scaleUnit_apply_fun, scaleUnit_apply_fun_left, MomentumEq]`, then
    `rw [DMul.hMul_scaleUnit, cast_scaleUnit, scaleUnit_injective]` (the last `rw` closes the goal by `rfl`).
    `simp [funext_iff, MomentumEq]` alone also works.
-/

/- E122 | Minkowski interval of an event | 2-3 min | Lorentz.Vector, minkowskiProduct, properTime, Real.sqrt, physlib
GOAL
  The event `p` has time coordinate `ct = 5` and position `(3, 0, 0)`. Show that its Minkowski square is
  `⟪p, p⟫ₘ = 5² - 3² = 16` and that the proper time from the origin to `p` is `√16 = 4`.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.Special.ProperTime

open Lorentz Vector

namespace E122

-- BEGIN SPEC
/-- The event `(ct, x, y, z) = (5, 3, 0, 0)`. -/
def p : SpaceTime 3 := fun
  | Sum.inl 0 => 5
  | Sum.inr 0 => 3
  | Sum.inr _ => 0
-- END SPEC

/- SKELETON · minkowski_p
  1. The product → coordinates (time part minus a sum over `Fin 3`):        R1
  2. Read off p's coordinates, expanding the spatial sum in the same `simp`
     (without R2 the indices stay variables and `simp` sticks on a `match`): R2, R3
  3. Finish the arithmetic `5 * 5 - 3 * 3 = 16`:                             R4
-/
-- BEGIN SPEC
theorem minkowski_p : ⟪p, p⟫ₘ = 16 :=
-- END SPEC
  sorry

/- SKELETON · properTime_p
  1. Unfold the proper time, clean up `p - 0`:                              R5, R6
  2. Reuse the first theorem; the goal becomes `√16 = 4`:                    rw [minkowski_p]
  3. Write `16` as `4 ^ 2` (ascribe `(16 : ℝ)`):                             R7
  4. Close `√(4 ^ 2) = 4`, proving `0 ≤ 4` on the spot:                      R8
-/
-- BEGIN SPEC
theorem properTime_p : SpaceTime.properTime 0 p = 4 :=
-- END SPEC
  sorry

end E122

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `⟪p, p⟫ₘ` is opaque until you turn it into coordinates; `properTime` is a `√` of a Minkowski product,
    so unfold it and reuse `minkowski_p` instead of recomputing.
H2. Part 1: `minkowskiProduct_toCoord`, then one `simp` that knows `p` and expands the sum over `Fin 3`,
    then `norm_num`. Part 2: unfold `SpaceTime.properTime`, remove `- 0`, rewrite with `minkowski_p`,
    then turn `√16` into `√(4 ^ 2)`: `norm_num` cannot evaluate a square root.
H3. `rw [minkowskiProduct_toCoord]; simp [p, Fin.sum_univ_three]; norm_num`, and
    `rw [SpaceTime.properTime, sub_zero, minkowski_p, show (16 : ℝ) = 4 ^ 2 by norm_num]`, then
    close `√(4 ^ 2) = 4` with `Real.sqrt_sq`.
-/

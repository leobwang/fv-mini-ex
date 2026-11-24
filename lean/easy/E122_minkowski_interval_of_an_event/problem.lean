/- E122 | Minkowski interval of an event | 2-3 min | Lorentz.Vector, minkowskiProduct, properTime, Real.sqrt, physlib
GOAL
  The event `p` has time coordinate `ct = 5` and position `(3, 0, 0)`. Show that its Minkowski square is
  `⟪p, p⟫ₘ = 5² - 3² = 16` and that the proper time from the origin to `p` is `√16 = 4`.

REFERENCE
  `SpaceTime 3 = Lorentz.Vector 3 = (Fin 1 ⊕ Fin 3 → ℝ)`: `p (Sum.inl 0)` is time, `p (Sum.inr i)` space.
  #check Lorentz.Vector.minkowskiProduct_toCoord -- ⟪p, q⟫ₘ = p (inl 0) * q (inl 0) - ∑ i, p (inr i) * q (inr i)
  example (p q : SpaceTime 3) : SpaceTime.properTime q p = √⟪p - q, p - q⟫ₘ := rfl
  #check Fin.sum_univ_three   -- ∑ i, f i = f 0 + f 1 + f 2   (a sum over `Fin 3`)
  #check Real.sqrt_sq         -- 0 ≤ x → √(x ^ 2) = x   (`√x` is notation for `Real.sqrt x`)
  example : (16 : ℝ) = 4 ^ 2 := by norm_num
  `⟪p, q⟫ₘ` is the Minkowski product with signature (+,−,−,−); it needs `open Lorentz Vector`.
NOTE: `rw [minkowskiProduct_toCoord]` first, then `simp [p, …]` reads off p; `norm_num [p]` sticks on p's `match`.
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

-- BEGIN SPEC
theorem minkowski_p : ⟪p, p⟫ₘ = 16 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem properTime_p : SpaceTime.properTime 0 p = 4 :=
-- END SPEC
  sorry

end E122

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. First turn `⟪p, p⟫ₘ` into coordinates; for the proper time, unfold the definition and reuse `minkowski_p`.
H2. After `minkowskiProduct_toCoord`, expand the spatial sum over `Fin 3` and let `simp [p]` read off the
    coordinates; finish the arithmetic with `norm_num`. For `properTime_p`, write `16` as `4 ^ 2`.
H3. `rw [minkowskiProduct_toCoord]; simp [p, Fin.sum_univ_three]; norm_num`, and
    `rw [SpaceTime.properTime, sub_zero, minkowski_p, show (16 : ℝ) = 4 ^ 2 by norm_num]`, then `Real.sqrt_sq`.
-/

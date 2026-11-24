/- E119 | Tight-binding bandwidth | 2-3 min | TightBindingChain, energyEigenvalue, abs, subtypes, physlib
GOAL
  In physlib's tight-binding chain (on-site energy `T.E0`, hopping `T.t`, lattice spacing `T.a`), the
  Bloch state of wavenumber `k` has energy `E(k) = E0 - 2t cos(ka)`. Show `|E(k) - E0| ≤ 2|t|`
  (the band has width `4|t|`).

REFERENCE
  #check CondensedMatter.TightBindingChain.energyEigenvalue  -- (T) (k : T.QuantaWaveNumber) : ℝ,  := T.E0 - 2 * T.t * Real.cos (↑k * T.a)
  #check Real.abs_cos_le_one       -- |Real.cos x| ≤ 1
  #check abs_mul                   -- |a * b| = |a| * |b|     (also `abs_neg : |-a| = |a|`, `abs_two : |2| = 2`)
  #check mul_le_of_le_one_right    -- 0 ≤ a → b ≤ 1 → a * b ≤ a
  example (x y z : ℝ) : x - y * z - x = -(y * z) := by ring
  `T.QuantaWaveNumber` is a `Set ℝ` (the allowed k); `k : T.QuantaWaveNumber` is a subtype element and
  `↑k : ℝ` its value. `unfold CondensedMatter.TightBindingChain.energyEigenvalue` exposes the formula.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace E119

-- BEGIN SPEC
theorem bandwidth (T : TightBindingChain) (k : T.QuantaWaveNumber) :
    |T.energyEigenvalue k - T.E0| ≤ 2 * |T.t| :=
-- END SPEC
  sorry

end E119

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `energyEigenvalue`; the `E0`s cancel, leaving `|-(2 t cos(ka))|`.
H2. Simplify that with a `show … by ring` rewrite, then split the absolute value of the product and use `|cos| ≤ 1`.
H3. `rw [show T.E0 - 2 * T.t * Real.cos (k * T.a) - T.E0 = -(2 * T.t * Real.cos (k * T.a)) by ring,
    abs_neg, abs_mul, abs_mul, abs_two]`, then `exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)`.
-/

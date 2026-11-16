/- E120 | Heat capacity is non-negative | 3 min | heatCapacity, fluctuation-dissipation, instance arguments, integral_nonneg, physlib
GOAL
  physlib defines the heat capacity `C(T) = dU/dT` (`U` = mean energy). Use its fluctuation-dissipation
  theorem `C = Var(E) / (k_B T²)` to show `C ≥ 0` for every finite canonical ensemble at `T > 0`.

REFERENCE
  #check CanonicalEnsemble.fluctuation_dissipation_theorem_finite
  --  (𝓒) [Nonempty ι] [MeasurableSingletonClass ι] [𝓒.IsFinite] (T) : 0 < T.val →
  --    𝓒.heatCapacity T = 𝓒.energyVariance T / (kB * ↑T.val ^ 2)
  #check MeasureTheory.integral_nonneg  -- 0 ≤ f → 0 ≤ ∫ x, f x ∂μ     (`0 ≤ f` means `∀ x, 0 ≤ f x`)
  #check div_nonneg        -- 0 ≤ a → 0 ≤ b → 0 ≤ a / b
  #check Constants.kB_pos  -- 0 < kB
  `𝓒.energyVariance T` is by definition `∫ i, (𝓒.energy i - 𝓒.meanEnergy T) ^ 2 ∂(𝓒.μProd T)`.
  Arguments in `[...]` are instances: Lean fills them from the context (all are hypotheses here).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Constants

namespace E120

-- BEGIN SPEC
theorem heatCapacity_nonneg {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite] (T : Temperature)
    (hT : 0 < T.val) : 0 ≤ 𝓒.heatCapacity T :=
-- END SPEC
  sorry

end E120

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do not differentiate anything: rewrite `heatCapacity` with the fluctuation-dissipation theorem.
H2. The result is `variance / (kB * T²)`: the numerator is an integral of a square, the denominator a product of positives.
H3. `rw [fluctuation_dissipation_theorem_finite 𝓒 T hT]`, `have := kB_pos`, then
    `exact div_nonneg (MeasureTheory.integral_nonneg fun _ => sq_nonneg _) (by positivity)`.
-/

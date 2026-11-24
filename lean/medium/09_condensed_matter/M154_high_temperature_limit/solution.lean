/- M154 | High-temperature limit | 10 min | Filter.Tendsto, continuity, fun_prop, physlib
GOAL
  As the inverse temperature `b → 0` (infinite temperature, kB = 1), every microstate of a finite
  system becomes equally likely: the Boltzmann probability `p_b i = exp (-b E i) / Z(b)` tends to
  `1 / |ι|`, where `|ι| = Fintype.card ι` is the number of microstates.

REFERENCE
  `Tendsto f (𝓝 a) (𝓝 L)` means `f x → L` as `x → a` (`𝓝 a`: neighbourhoods of `a`, from `open Topology`).
  #check Continuous.tendsto  -- Continuous f → ∀ x, Tendsto f (𝓝 x) (𝓝 (f x))
  #check Continuous.div      -- Continuous f → Continuous g → (∀ x, g x ≠ 0) → Continuous (f / g)
  #check CanonicalEnsemble.probabilityBetaReal  -- 𝓒.probabilityBetaReal b i = exp (-b * 𝓒.energy i) / Z(b)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  example (E : ℝ) : Continuous (fun b : ℝ => Real.exp (-b * E)) := by fun_prop
  `simpa [defs] using h` simplifies both `h` and the goal (here `exp 0 = 1`, `∑ i, 1 = card ι`).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real Filter Topology

namespace M154

-- BEGIN SPEC
theorem high_temperature_limit {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (i : ι) :
    Tendsto (fun b => 𝓒.probabilityBetaReal b i) (𝓝 0) (𝓝 (1 / Fintype.card ι)) :=
-- END SPEC
  by
    have hc : Continuous (fun b => 𝓒.probabilityBetaReal b i) := by
      unfold probabilityBetaReal mathematicalPartitionFunctionBetaReal
      exact Continuous.div (by fun_prop) (by fun_prop)
        (fun b => (𝓒.mathematicalPartitionFunctionBetaReal_pos b).ne')
    simpa [probabilityBetaReal, mathematicalPartitionFunctionBetaReal] using hc.tendsto 0

end M154

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `b ↦ p_b i` is continuous, so its limit at `0` is its value at `0`, which is `1 / card ι`.
H2. Prove `hc : Continuous (fun b => 𝓒.probabilityBetaReal b i)`: unfold both definitions; it is a
    quotient of continuous functions with a nowhere-zero denominator. Then evaluate `hc.tendsto 0`.
H3. `have hc : Continuous (fun b => 𝓒.probabilityBetaReal b i)`, proved with `Continuous.div`; its
    nonzero-denominator argument comes from `mathematicalPartitionFunctionBetaReal_pos`. Then `hc.tendsto 0`.
-/

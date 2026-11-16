/- M150 | The Boltzmann distribution | 5-10 min | probabilityBetaReal, Finset.sum_div, positivity, physlib
GOAL
  A finite system `𝓒 : CanonicalEnsemble ι` has microstates `i : ι` with energies `𝓒.energy i`. At
  inverse temperature `b` (units with kB = 1) the Boltzmann weights `p i = exp (-b E i) / Z(b)`, where
  `Z(b) = ∑ i, exp (-b E i)`, form a probability distribution: every `p i > 0` and `∑ i, p i = 1`.

REFERENCE
  #check CanonicalEnsemble.probabilityBetaReal  -- 𝓒.probabilityBetaReal b i = exp (-b * 𝓒.energy i) / Z(b)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  #check Finset.sum_div  -- (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a
  #check div_self        -- a ≠ 0 → a / a = 1
  example (x y : ℝ) (hy : 0 < y) : 0 < Real.exp x / y := by positivity  -- uses `hy` from context
  `unfold CanonicalEnsemble.probabilityBetaReal` (or `simp only [probabilityBetaReal]`) exposes the
  definition; `∑ i, f i` is `Finset.univ.sum f`, so `Finset` lemmas apply with `s = univ`.
BANNED: sum_probability_eq_one, probability_nonneg_finite
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M150

-- BEGIN SPEC
theorem boltzmann_is_distribution {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) :
    (∀ i, 0 < 𝓒.probabilityBetaReal b i) ∧ ∑ i, 𝓒.probabilityBetaReal b i = 1 :=
-- END SPEC
  sorry

end M150

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both parts only need `Z(b) > 0`: get it once with `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b`.
H2. Positivity: unfold `probabilityBetaReal`, then `positivity`. Sum: pull the common denominator out
    of the sum (`← Finset.sum_div`); the numerator is then `Z(b)` by definition.
H3. `simp only [probabilityBetaReal, ← Finset.sum_div]` leaves `(∑ i, exp (-b * 𝓒.energy i)) / Z(b) = 1`;
    close it with `div_self hZ.ne'` (`exact` sees through the definition of `Z(b)`).
-/

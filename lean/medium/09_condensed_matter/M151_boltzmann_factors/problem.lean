/- M151 | Boltzmann factors | 10 min | probabilityBetaReal, ratios, monotonicity of exp, physlib
GOAL
  For Boltzmann probabilities `p i = exp (-b E i) / Z(b)` (`E i = 𝓒.energy i`, `b` the inverse
  temperature, kB = 1): the ratio `p j / p i` is `exp (-b (E j - E i))`, so `Z(b)` cancels; and at
  `b ≥ 0` a lower-energy state is at least as likely as a higher-energy one.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M151

/- SKELETON · boltzmann_ratio
  1. Prove `Z(b) ≠ 0` first:                                                R1 → R2
       hZ : 𝓒.mathematicalPartitionFunctionBetaReal b ≠ 0
  2. Unfold both probabilities into `rexp (-b * E _) / Z(b)`:               R3
  3. Cancel the common `Z(b)` with `hZ`:                                    R4
  4. Fold `rexp _ / rexp _` into one exponential:                           R5
  5. The two exponents agree only up to ring algebra; close:                R6
-/
-- BEGIN SPEC
theorem boltzmann_ratio {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) (i j : ι) :
    𝓒.probabilityBetaReal b j / 𝓒.probabilityBetaReal b i =
      Real.exp (-b * (𝓒.energy j - 𝓒.energy i)) :=
-- END SPEC
  sorry

/- SKELETON · lower_energy_more_likely
  1. Prove `0 < Z(b)` first:                                                R1
  2. Unfold both probabilities:                                             R3
  3. Drop the common positive denominator (not `gcongr`, see Traps):        R7
  4. Compare exponents instead of exponentials:                             R8
  5. Close `-b * E j ≤ -b * E i` from `hb` and `hE`:                        R9
-/
-- BEGIN SPEC
theorem lower_energy_more_likely {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) (hb : 0 ≤ b) (i j : ι) (hE : 𝓒.energy i ≤ 𝓒.energy j) :
    𝓒.probabilityBetaReal b j ≤ 𝓒.probabilityBetaReal b i :=
-- END SPEC
  sorry

end M151

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both probabilities have the same denominator `Z(b)`, and `Z(b) > 0` (so `Z(b) ≠ 0`).
H2. Ratio: unfold, cancel the common denominator, then fold the two exponentials into one and match
    exponents. Ordering: unfold, compare numerators only, then compare exponents.
H3. With `hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b`:
    `rw [div_div_div_cancel_right₀ hZ.ne', ← Real.exp_sub]` then `ring_nf`, and
    `rw [div_le_div_iff_of_pos_right hZ, Real.exp_le_exp]` then `nlinarith`.
-/

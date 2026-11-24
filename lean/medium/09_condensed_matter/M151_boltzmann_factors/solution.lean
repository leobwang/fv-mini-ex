/- M151 | Boltzmann factors | 10 min | probabilityBetaReal, ratios, monotonicity of exp, physlib
GOAL
  For Boltzmann probabilities `p i = exp (-b E i) / Z(b)` (`E i = 𝓒.energy i`, `b` the inverse
  temperature, kB = 1): the ratio `p j / p i` is `exp (-b (E j - E i))`, so `Z(b)` cancels; and at
  `b ≥ 0` a lower-energy state is at least as likely as a higher-energy one.

REFERENCE
  #check CanonicalEnsemble.probabilityBetaReal  -- 𝓒.probabilityBetaReal b i = exp (-b * 𝓒.energy i) / Z(b)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  #check div_div_div_cancel_right₀  -- c ≠ 0 → a / c / (b / c) = a / b
  #check Real.exp_sub               -- exp (x - y) = exp x / exp y
  #check Real.exp_le_exp            -- exp x ≤ exp y ↔ x ≤ y
  #check div_le_div_iff_of_pos_right  -- 0 < c → (a / c ≤ b / c ↔ a ≤ b)
  example (b x y : ℝ) (hb : 0 ≤ b) (h : x ≤ y) : -b * y ≤ -b * x := by nlinarith
  `rw [← Real.exp_sub]` folds `exp x / exp y` back into `exp (x - y)`; `ring_nf` then matches exponents.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M151

-- BEGIN SPEC
theorem boltzmann_ratio {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) (i j : ι) :
    𝓒.probabilityBetaReal b j / 𝓒.probabilityBetaReal b i =
      Real.exp (-b * (𝓒.energy j - 𝓒.energy i)) :=
-- END SPEC
  by
    have hZ := (𝓒.mathematicalPartitionFunctionBetaReal_pos b).ne'
    simp only [probabilityBetaReal]
    rw [div_div_div_cancel_right₀ hZ, ← Real.exp_sub]
    ring_nf

-- BEGIN SPEC
theorem lower_energy_more_likely {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) (hb : 0 ≤ b) (i j : ι) (hE : 𝓒.energy i ≤ 𝓒.energy j) :
    𝓒.probabilityBetaReal b j ≤ 𝓒.probabilityBetaReal b i :=
-- END SPEC
  by
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
    unfold probabilityBetaReal
    -- WHY: `gcongr` would pick the pattern `exp (-b * _)` and ask for `0 ≤ -b`; compare numerators instead.
    rw [div_le_div_iff_of_pos_right hZ, Real.exp_le_exp]
    nlinarith

end M151

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both probabilities have the same denominator `Z(b)`, and `Z(b) ≠ 0`.
H2. Ratio: unfold, cancel the common denominator, then combine the two exponentials into one.
    Ordering: unfold, compare numerators only, then compare exponents.
H3. With `hZ : 0 < Z(b)`: `rw [div_div_div_cancel_right₀ hZ.ne', ← Real.exp_sub]` and
    `rw [div_le_div_iff_of_pos_right hZ, Real.exp_le_exp]`; each leaves an exponent goal to finish.
-/

/- M160 | Mean energy from log Z | 15-20 min | HasDerivAt.fun_sum, HasDerivAt.exp, HasDerivAt.log, physlib
GOAL
  For any finite system `𝓒` and inverse temperature `b` (units kB = 1), `U(b) = -d/db log Z(b)`, stated as
  `HasDerivAt`. Derive `Z'(b) = -∑ i, E i exp (-b E i)` yourself, term by term.

REFERENCE
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.meanEnergyBetaReal  -- U(b) = ∑ i, E i * p b i,  p b i = exp (-b * E i) / Z(b)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  #check HasDerivAt.fun_sum  -- (∀ i ∈ u, HasDerivAt (A i) (A' i) x) → HasDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x
  #check HasDerivAt.exp      -- HasDerivAt f f' x → HasDerivAt (fun x => exp (f x)) (exp (f x) * f') x
  #check HasDerivAt.log      -- HasDerivAt f f' x → f x ≠ 0 → HasDerivAt (fun y => log (f y)) (f' / f x) x
  #check HasDerivAt.congr_deriv  -- HasDerivAt f f' x → f' = g' → HasDerivAt f g' x
  example (b c : ℝ) : HasDerivAt (fun x => -x * c) (-1 * c) b := (hasDerivAt_id' b).neg.mul_const c
  #check Finset.sum_neg_distrib  -- ∑ x ∈ s, -f x = -∑ x ∈ s, f x
  `HasDerivAt f f' x`: f is differentiable at x with derivative f'. Dot notation chains rules: `h.exp`, `h.log hne`.
BANNED: deriv_mathematicalPartitionFunctionBetaReal, differentiable_mathematicalPartitionFunctionBetaReal, meanEnergy_eq_neg_deriv_log_mathZ_of_beta, meanEnergy_eq_neg_deriv_log_Z_of_beta
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M160

-- BEGIN SPEC
theorem meanEnergy_eq_neg_dlogZ {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) :
    HasDerivAt (fun x => Real.log (𝓒.mathematicalPartitionFunctionBetaReal x))
      (-𝓒.meanEnergyBetaReal b) b :=
-- END SPEC
  by
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
    have hd : HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal
        (-∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b := by
      unfold mathematicalPartitionFunctionBetaReal
      rw [← Finset.sum_neg_distrib]
      apply HasDerivAt.fun_sum
      intro i _
      -- WHY: `congr_deriv`, not `convert … using 1`, which leaves an instance-equality side goal.
      exact (((hasDerivAt_id' b).neg.mul_const (𝓒.energy i)).exp).congr_deriv (by simp; ring)
    refine (hd.log hZ.ne').congr_deriv ?_
    simp only [meanEnergyBetaReal, probabilityBetaReal, ← mul_div_assoc, ← Finset.sum_div]
    ring

end M160

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two steps: the derivative of `Z` itself (a finite sum of exponentials), then the chain rule for
    `log`, which gives `Z'(b) / Z(b)`; that ratio is `-U(b)` after pulling `/ Z(b)` out of the sum.
H2. `have hd : HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal (-∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b`:
    `unfold mathematicalPartitionFunctionBetaReal`, `rw [← Finset.sum_neg_distrib]`, `apply HasDerivAt.fun_sum`.
    Then `refine (hd.log hZ.ne').congr_deriv ?_`.
H3. Each term: `(((hasDerivAt_id' b).neg.mul_const (𝓒.energy i)).exp).congr_deriv (by simp; ring)`.
    The last goal: `simp only [meanEnergyBetaReal, probabilityBetaReal, ← mul_div_assoc, ← Finset.sum_div]; ring`.
-/

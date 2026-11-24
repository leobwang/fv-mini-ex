/- M160 | Mean energy from log Z | 15-20 min | HasDerivAt.fun_sum, HasDerivAt.exp, HasDerivAt.log, physlib
GOAL
  For any finite system `𝓒` and inverse temperature `b` (units kB = 1), `U(b) = -d/db log Z(b)`, stated as
  `HasDerivAt`. Derive `Z'(b) = -∑ i, E i exp (-b E i)` yourself, term by term.
BANNED: deriv_mathematicalPartitionFunctionBetaReal, differentiable_mathematicalPartitionFunctionBetaReal, meanEnergy_eq_neg_deriv_log_mathZ_of_beta, meanEnergy_eq_neg_deriv_log_Z_of_beta

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M160

/- SKELETON · meanEnergy_eq_neg_dlogZ
  1. Fact first:  hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal b                  R1
  2. MILESTONE (prove it first, used in step 3):
       hd : HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal
              (-∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b
     a. unfold the bare function `Z`, move the minus into the sum:            R2 → R3
     b. one goal per term:                                                    R4 → R5
     c. build the term's derivative from the identity, outward:
          `fun y => y` → `-y` → `-y * 𝓒.energy i` → `rexp (-y * 𝓒.energy i)`  R6 → R7 → R8 → R9
        match it to the claimed derivative, then fix the side equation:     R10, R11, ring
  3. Chain rule for `log` applied to `hd` (with `hZ`), matched to `-U(b)`:     R12 with R13, R10
  4. The equation `Z'(b) / Z(b) = -U(b)`: unfold `U` and `p`, pull `/ Z(b)` out of
     the sum, finish:                                                         R14, R15, R16 → R17, R18
-/
-- BEGIN SPEC
theorem meanEnergy_eq_neg_dlogZ {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) :
    HasDerivAt (fun x => Real.log (𝓒.mathematicalPartitionFunctionBetaReal x))
      (-𝓒.meanEnergyBetaReal b) b :=
-- END SPEC
  sorry

end M160

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two steps: the derivative of `Z` itself (a finite sum of exponentials, differentiated term by term),
    then the chain rule for `log`, which gives `Z'(b) / Z(b)`; that ratio is `-U(b)` once `/ Z(b)` is
    pulled out of the sum in `U(b) = ∑ i, E i * (exp (-b E i) / Z(b))`.
H2. Milestone `hd : HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal (-∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b`:
    `unfold mathematicalPartitionFunctionBetaReal`, `rw [← Finset.sum_neg_distrib]`, `apply HasDerivAt.fun_sum`,
    `intro i _`; build each term from `hasDerivAt_id' b` with `.neg`, `.mul_const`, `.exp` and match it with
    `.congr_deriv`. Then `refine (hd.log hZ.ne').congr_deriv ?_` leaves an equation of real numbers.
H3. Each term: `(((hasDerivAt_id' b).neg.mul_const (𝓒.energy i)).exp).congr_deriv (by simp; ring)`.
    The last goal: `simp only [meanEnergyBetaReal, probabilityBetaReal, ← mul_div_assoc, ← Finset.sum_div]; ring`.
-/

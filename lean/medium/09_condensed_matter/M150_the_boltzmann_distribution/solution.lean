/- M150 | The Boltzmann distribution | 5-10 min | probabilityBetaReal, Finset.sum_div, positivity, physlib
GOAL
  A finite system `𝓒 : CanonicalEnsemble ι` has microstates `i : ι` with energies `𝓒.energy i`. At
  inverse temperature `b` (units with kB = 1) the Boltzmann weights `p i = exp (-b E i) / Z(b)`, where
  `Z(b) = ∑ i, exp (-b E i)`, form a probability distribution: every `p i > 0` and `∑ i, p i = 1`.

BANNED: sum_probability_eq_one, probability_nonneg_finite

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M150

/- SKELETON · boltzmann_is_distribution
  1. Get the one fact both halves need, BEFORE splitting:                    R1
       hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal b
  2. Split the conjunction; the first goal gains `i : ι`:                     R2
  3. Goal `0 < 𝓒.probabilityBetaReal b i`:
       expose exp (-b * E i) / Z(b)                                          R3
       close it (uses hZ from the context)                                   R4
  4. Goal `∑ i, 𝓒.probabilityBetaReal b i = 1`:
       unfold under the sum, then pull the common denominator Z(b) out       R3, R5
       (one `simp only [...]` call can do both)
       the numerator is now Z(b) by definition (no step needed, R6 shows it)  R6
       close `Z(b) / Z(b) = 1` from hZ                                       R7 → R8
-/
-- BEGIN SPEC
theorem boltzmann_is_distribution {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) :
    (∀ i, 0 < 𝓒.probabilityBetaReal b i) ∧ ∑ i, 𝓒.probabilityBetaReal b i = 1 :=
-- END SPEC
  by
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
    refine ⟨fun i => by unfold probabilityBetaReal; positivity, ?_⟩
    simp only [probabilityBetaReal, ← Finset.sum_div]
    exact div_self hZ.ne'

end M150

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both halves only need `Z(b) > 0`. physlib proves it: get it once, before splitting, with
    `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` (R1).
H2. Split with `refine ⟨fun i => ?_, ?_⟩` (R2). Positivity: unfold `probabilityBetaReal`, then `positivity`
    (R3, R4). Sum: unfold, then pull the common denominator out of the sum with `← Finset.sum_div` (R5);
    the numerator is then `Z(b)` by definition (R6).
H3. `simp only [probabilityBetaReal, ← Finset.sum_div]` leaves `(∑ i, rexp (-b * 𝓒.energy i)) / Z(b) = 1`;
    close it with `exact div_self hZ.ne'` (R7, R8; `exact` sees through the definition of `Z(b)`).
-/

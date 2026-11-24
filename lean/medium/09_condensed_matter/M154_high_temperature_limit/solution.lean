/- M154 | High-temperature limit | 10 min | Filter.Tendsto, continuity, fun_prop, physlib
GOAL
  As the inverse temperature `b → 0` (infinite temperature, kB = 1), every microstate of a finite
  system becomes equally likely: the Boltzmann probability `p_b i = exp (-b E i) / Z(b)` tends to
  `1 / |ι|`, where `|ι| = Fintype.card ι` is the number of microstates.

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real Filter Topology

namespace M154

/- SKELETON · high_temperature_limit
  1. Milestone first: `b ↦ p_b i` is continuous, as a fact (TACTIC_STATES, `have … := by`):
       hc : Continuous (fun b => 𝓒.probabilityBetaReal b i)
     a. unfold the probability, then the partition function Z:             R1, R2
     b. a quotient of continuous functions → three goals:                   R3
     c. numerator, denominator continuous:                                  R4, R4
     d. denominator never 0: for each `b` (`intro b`, or `fun b => …`),
        the fact 0 < Z(b), flipped to Z(b) ≠ 0:                            R5 → R6
  2. Continuity at 0 gives a limit at 0, with the limit written `p_0 i`:     R7
  3. Evaluate `p_0 i` to `1 / card ι` on both sides and close; give `simpa`
     both physlib definitions, and it does R8, R9, R10 by itself:           R11
-/
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
H1. A continuous function's limit at a point is its value there. So it is enough to show that
    `b ↦ p_b i` is continuous and that `p_0 i = exp 0 / ∑ j, exp 0 = 1 / |ι|`.
H2. `have hc : Continuous (fun b => 𝓒.probabilityBetaReal b i)`: unfold both definitions, then
    `Continuous.div` (two `fun_prop` goals and a nonzero denominator from
    `mathematicalPartitionFunctionBetaReal_pos`). Then simplify the limit in `hc.tendsto 0`.
H3. The denominator argument of `Continuous.div` is
    `fun b => (𝓒.mathematicalPartitionFunctionBetaReal_pos b).ne'`, and the last line is
    `simpa [probabilityBetaReal, mathematicalPartitionFunctionBetaReal] using hc.tendsto 0`.
-/

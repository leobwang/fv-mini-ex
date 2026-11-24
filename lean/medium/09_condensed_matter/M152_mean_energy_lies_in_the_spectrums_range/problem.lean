/- M152 | Mean energy lies in the spectrum's range | 10 min | meanEnergyBetaReal, Finset.sum_le_sum, calc, physlib
GOAL
  If every energy level satisfies `m ≤ E i ≤ M`, then the thermal mean energy
  `U(b) = ∑ i, E i * p i` (with Boltzmann weights `p i = exp (-b E i) / Z(b)`, kB = 1) also lies in
  `[m, M]`, at every inverse temperature `b`, including negative ones.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M152

/- SKELETON · meanEnergy_bounds
  Write `p i` for `𝓒.probabilityBetaReal b i`, `Z` for `𝓒.mathematicalPartitionFunctionBetaReal b`.
  1. Three facts first, all used in both halves:
       hZ : 0 < Z                                                           R1
       hp : ∀ i, 0 ≤ p i               intro i, unfold p, then close        R2 → R3 (needs hZ)
       h1 : ∑ i, p i = 1               unfold p, pull out `/ Z`, cancel     R2 → R4 → R7 (R6 with R5)
  2. Unfold the mean energy, then split the `∧`:                            R8, constructor
  3. Lower half `m ≤ ∑ i, E i * p i`, a two-step calc:                      R9
       m = ∑ i, m * p i                pull `m` out, rw [h1], drop `* 1`    R10, rw [h1], R11
       _ ≤ _                           term by term, using hm i and hp i    R12 → R13
  4. Upper half `∑ i, E i * p i ≤ M`: the mirror image, middle term `∑ i, M * p i`,
     the `≤` step first (hM i, hp i), then the `=` step:                    R9, R12 → R13, R10, rw [h1], R11
-/
-- BEGIN SPEC
theorem meanEnergy_bounds {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b m M : ℝ) (hm : ∀ i, m ≤ 𝓒.energy i) (hM : ∀ i, 𝓒.energy i ≤ M) :
    m ≤ 𝓒.meanEnergyBetaReal b ∧ 𝓒.meanEnergyBetaReal b ≤ M :=
-- END SPEC
  sorry

end M152

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `U(b)` is a weighted average of the energies: the weights `p i` are non-negative and sum to 1, and an
    average of numbers in `[m, M]` stays in `[m, M]`. The sign of `b` never matters.
H2. Prove `hZ`, `hp : ∀ i, 0 ≤ p i` and `h1 : ∑ i, p i = 1` first. Unfold `meanEnergyBetaReal`, split, and
    in each half `calc` through `∑ i, m * p i` (resp. `∑ i, M * p i`): one step is `rw` with
    `← Finset.mul_sum`, `h1`, `mul_one`; the other compares the sums term by term.
H3. `h1`: `simp only [probabilityBetaReal, ← Finset.sum_div]` then `exact div_self hZ.ne'`.
    Lower half: `calc m = ∑ i, m * 𝓒.probabilityBetaReal b i := by rw [← Finset.mul_sum, h1, mul_one]`
    then `_ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (hp i)`; mirror it for `M`.
-/

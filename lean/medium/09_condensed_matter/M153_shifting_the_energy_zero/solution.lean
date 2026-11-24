/- M153 | Shifting the energy zero | 10-15 min | structure update, Real.exp_add, funext, physlib
GOAL
  `shift 𝓒 c` is the same system with every energy level raised by `c`. Show (kB = 1, inverse
  temperature `b`): `Z(b)` gets multiplied by `exp (-b c)`, all Boltzmann probabilities are
  unchanged, and the mean energy `U(b) = ∑ i, E i * p i` goes up by exactly `c`.

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M153

-- BEGIN SPEC
/-- The same system with every energy level shifted by `c`. -/
noncomputable def shift {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (c : ℝ) :
    CanonicalEnsemble ι :=
  { 𝓒 with energy := fun i => 𝓒.energy i + c, energy_measurable := by fun_prop }
-- END SPEC

/- SKELETON · shift_Z
  1. Unfold both partition functions and the shifted energies, push `exp (-b * c)` into the
     right-hand sum, merge the products of exponentials (one `simp only [...]` can do all four):
                                                                            R1, R2, R3, R4
  2. Compare the two sums term by term:                                     R5 → R6
  3. Close `rexp (-b * (𝓒.energy i + c)) = rexp (-b * c + -b * 𝓒.energy i)`:  R7
-/
-- BEGIN SPEC
theorem shift_Z {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (c b : ℝ) :
    (shift 𝓒 c).mathematicalPartitionFunctionBetaReal b =
      Real.exp (-b * c) * 𝓒.mathematicalPartitionFunctionBetaReal b :=
-- END SPEC
  by
    simp only [mathematicalPartitionFunctionBetaReal, shift, Finset.mul_sum, ← Real.exp_add]
    congr 1
    funext i
    ring_nf

/- SKELETON · shift_probability
  1. Equation of functions → one microstate `i`:                            R6
  2. Unfold the shifted probability, replace its `Z` by Part 1, unfold the other side:
                                                                            R8, rw [shift_Z], R8
  3. The shifted energy as `𝓒.energy i + c`:                                R9, then rw [hE]
  4. Reshape the exponent into a sum `-b * c + -b * 𝓒.energy i`:            R10
  5. Split the exponential:                                                 R11
  6. Cancel the common factor `rexp (-b * c)`, its `≠ 0` proof as argument:  R12 with R13
-/
-- BEGIN SPEC
theorem shift_probability {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (c b : ℝ) :
    (shift 𝓒 c).probabilityBetaReal b = 𝓒.probabilityBetaReal b :=
-- END SPEC
  by
    funext i
    rw [probabilityBetaReal, shift_Z, probabilityBetaReal]
    have hE : (shift 𝓒 c).energy i = 𝓒.energy i + c := rfl
    rw [hE, show -b * (𝓒.energy i + c) = -b * c + -b * 𝓒.energy i by ring, Real.exp_add,
      mul_div_mul_left _ _ (Real.exp_pos _).ne']

/- SKELETON · shift_meanEnergy
  1. Facts first:
       hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal b                   R14
       h1 : ∑ i, 𝓒.probabilityBetaReal b i = 1      proof: R15 → R16 → R17 (with hZ.ne', R13)
  2. Unfold both mean energies, then replace the shifted probabilities
     by Part 2 (before unfolding `shift`, see Traps):                       R18, R19 with shift_probability
  3. Unfold the shifted energies:                                           R2
  4. Split `∑ (𝓒.energy x + c) * p x`, pull `c` out, use `h1`, finish:       R20 → R21 → R22, simp only [h1], R23
-/
-- BEGIN SPEC
theorem shift_meanEnergy {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (c b : ℝ) :
    (shift 𝓒 c).meanEnergyBetaReal b = 𝓒.meanEnergyBetaReal b + c :=
-- END SPEC
  by
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
    have h1 : ∑ i, 𝓒.probabilityBetaReal b i = 1 := by
      simp only [probabilityBetaReal, ← Finset.sum_div]
      exact div_self hZ.ne'
    simp only [meanEnergyBetaReal, shift_probability]
    simp only [shift, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_one]

end M153

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `exp (-b (E + c)) = exp (-b c) · exp (-b E)`: the shift multiplies every Boltzmann weight by the
    same factor. Work on unfolded definitions (R1, R8/R15, R18); each part is then a lemma for the next.
H2. `shift_Z`: unfold, push the constant into the sum, merge exponentials, compare termwise.
    `shift_probability`: `funext i`, unfold, `rw [shift_Z]`, split the exponential, cancel `exp (-b c)`.
    `shift_meanEnergy`: prove `∑ i, p i = 1` first; rewrite with `shift_probability`, split
    `(E i + c) * p i`, pull `c` out of the sum.
H3. `simp only [mathematicalPartitionFunctionBetaReal, shift, Finset.mul_sum, ← Real.exp_add]; congr 1; funext i; ring_nf`;
    `rw [show -b * (𝓒.energy i + c) = -b * c + -b * 𝓒.energy i by ring, Real.exp_add, mul_div_mul_left _ _ (Real.exp_pos _).ne']`;
    `simp only [shift, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_one]`.
-/

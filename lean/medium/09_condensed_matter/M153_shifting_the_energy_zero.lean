/- M153 | Shifting the energy zero | 10-15 min | structure update, Real.exp_add, funext, physlib
GOAL
  `shift 𝓒 c` is the same system with every energy level raised by `c`. Show (kB = 1, inverse
  temperature `b`): `Z(b)` gets multiplied by `exp (-b c)`, all Boltzmann probabilities are
  unchanged, and the mean energy `U(b) = ∑ i, E i * p i` goes up by exactly `c`.

REFERENCE
  `{ 𝓒 with energy := f, energy_measurable := pf }` copies the structure `𝓒` and replaces two fields;
  so `(shift 𝓒 c).energy i = 𝓒.energy i + c` holds by `rfl` (`simp only [shift]` also unfolds it).
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.probabilityBetaReal  -- 𝓒.probabilityBetaReal b i = exp (-b * 𝓒.energy i) / Z(b)
  #check CanonicalEnsemble.meanEnergyBetaReal   -- U(b) = ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i
  #check Real.exp_add       -- exp (x + y) = exp x * exp y
  #check mul_div_mul_left   -- (a b : G₀) : c ≠ 0 → c * a / (c * b) = a / b
  #check Finset.mul_sum     -- a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
  #check Finset.sum_add_distrib  -- ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i
  `funext i` proves `f = g` between functions; `congr 1; funext i` compares two sums termwise.
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

-- BEGIN SPEC
theorem shift_Z {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (c b : ℝ) :
    (shift 𝓒 c).mathematicalPartitionFunctionBetaReal b =
      Real.exp (-b * c) * 𝓒.mathematicalPartitionFunctionBetaReal b :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem shift_probability {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (c b : ℝ) :
    (shift 𝓒 c).probabilityBetaReal b = 𝓒.probabilityBetaReal b :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem shift_meanEnergy {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (c b : ℝ) :
    (shift 𝓒 c).meanEnergyBetaReal b = 𝓒.meanEnergyBetaReal b + c :=
-- END SPEC
  sorry

end M153

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `exp (-b (E + c)) = exp (-b c) · exp (-b E)`: the shift factors out of every Boltzmann weight.
H2. `shift_Z`: unfold both sums, push the constant inside with `Finset.mul_sum`, merge exponentials,
    compare termwise. `shift_probability`: `funext i`, use `shift_Z`, cancel `exp (-b c)`.
    `shift_meanEnergy`: rewrite with `shift_probability`, split `(E i + c) * p i`, and use `∑ p = 1`.
H3. `simp only [mathematicalPartitionFunctionBetaReal, shift, Finset.mul_sum, ← Real.exp_add]; congr 1; funext i; ring_nf`;
    `rw [show -b * (𝓒.energy i + c) = -b * c + -b * 𝓒.energy i by ring, Real.exp_add, mul_div_mul_left _ _ (Real.exp_pos _).ne']`.
-/

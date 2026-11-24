/- M173 | Independent subsystems | 15-20 min | product system, Fintype.sum_prod_type, Finset.sum_mul_sum, physlib
GOAL
  Two non-interacting finite systems form physlib's product system `𝓒 + 𝓒'` (microstates `ι × ι'`,
  energies add). From the finite-sum formulas, show `Z = Z₁ Z₂` and `U = U₁ + U₂`; for `U` first
  prove the helper `(𝓒 + 𝓒').probability T (i, j) = 𝓒.probability T i * 𝓒'.probability T j`.

REFERENCE
  #check CanonicalEnsemble.energy_add_apply  -- (𝓒 + 𝓒1).energy i = 𝓒.energy i.1 + 𝓒1.energy i.2
  #check CanonicalEnsemble.partitionFunction_of_fintype  -- Z T = ∑ i, exp (-T.β * 𝓒.energy i)
  #check CanonicalEnsemble.meanEnergy_of_fintype   -- U T = ∑ i, 𝓒.energy i * 𝓒.probability T i
  #check CanonicalEnsemble.probability  -- p T i = exp (-β E i) / mathematicalPartitionFunction T
  #check CanonicalEnsemble.mathematicalPartitionFunction_of_fintype  -- = ∑ i, exp (-β E i)
  #check CanonicalEnsemble.sum_probability_eq_one  -- ∑ i, 𝓒.probability T i = 1
  #check Fintype.sum_prod_type  -- ∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)
  #check Finset.sum_mul_sum     -- (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j
  #check Real.exp_add           -- exp (x + y) = exp x * exp y   (also `div_mul_div_comm`, `Finset.sum_comm`)
BANNED: partitionFunction_add, mathematicalPartitionFunction_add, probability_add, meanEnergy_add, μBolt_add, μProd_add, helmholtzFreeEnergy_add, try?
NOTE: `Temperature.β_toReal : (T.β : ℝ) = 1 / (kB * T.toReal)`; the `IsFinite` instance of `𝓒 + 𝓒'` is anonymous (never name it).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M173

-- BEGIN SPEC
theorem Z_mul {ι ι' : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace ι] [MeasurableSpace ι']
    [MeasurableSingletonClass ι] [MeasurableSingletonClass ι']
    (𝓒 : CanonicalEnsemble ι) (𝓒' : CanonicalEnsemble ι') [𝓒.IsFinite] [𝓒'.IsFinite]
    (T : Temperature) :
    (𝓒 + 𝓒').partitionFunction T = 𝓒.partitionFunction T * 𝓒'.partitionFunction T :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem U_add {ι ι' : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace ι] [MeasurableSpace ι']
    [MeasurableSingletonClass ι] [MeasurableSingletonClass ι'] [Nonempty ι] [Nonempty ι']
    (𝓒 : CanonicalEnsemble ι) (𝓒' : CanonicalEnsemble ι') [𝓒.IsFinite] [𝓒'.IsFinite]
    (T : Temperature) :
    (𝓒 + 𝓒').meanEnergy T = 𝓒.meanEnergy T + 𝓒'.meanEnergy T :=
-- END SPEC
  sorry

end M173

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rewrite every `Z` and `U` with its `_of_fintype` formula, then split the sum over `ι × ι'`
    into a double sum.
H2. `Z_mul`: the Boltzmann weight factorises, `exp (-β (E i + E' j)) = exp (-β E i) * exp (-β E' j)`.
    `U_add`: first prove the helper `(𝓒 + 𝓒').probability T (i, j) = 𝓒.probability T i * 𝓒'.probability T j`;
    then `(E i + E' j) p i p' j` splits into two double sums, and each collapses via `∑ p = 1`.
H3. `rw [partitionFunction_of_fintype, partitionFunction_of_fintype, partitionFunction_of_fintype,
    Fintype.sum_prod_type, Finset.sum_mul_sum]`; helper: `simp only [probability,
    mathematicalPartitionFunction_of_fintype, Fintype.sum_prod_type, energy_add_apply, mul_add,
    Real.exp_add, ← Finset.sum_mul_sum, div_mul_div_comm]`.
-/

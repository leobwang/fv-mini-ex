/- M173 | Independent subsystems | 15-20 min | product system, Fintype.sum_prod_type, Finset.sum_mul_sum, physlib
GOAL
  Two non-interacting finite systems form physlib's product system `𝓒 + 𝓒'` (microstates `ι × ι'`,
  energies add). From the finite-sum formulas, show `Z = Z₁ Z₂` and `U = U₁ + U₂`; for `U` first
  prove the helper `(𝓒 + 𝓒').probability T (i, j) = 𝓒.probability T i * 𝓒'.probability T j`.

BANNED: partitionFunction_add, mathematicalPartitionFunction_add, probability_add, meanEnergy_add, μBolt_add, μProd_add, helmholtzFreeEnergy_add, try?

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M173

/- SKELETON · Z_mul
  1. Each `partitionFunction` → its finite sum; one `rw` per ensemble (3×):      R1, R1, R1
  2. Left: the sum over `ι × ι'` → a double sum:                                 R2
  3. Right: the product of two sums → a double sum of products:                  R3
  4. Both sides are double sums over the same indices: reduce to one summand,
     nesting R4 twice (context gains `i`, `j`):                                  R4, R4
  5. In the summand: product energy → sum, distribute `-↑T.β`, split `exp`
     (`rw` closes the rest by `rfl`):                                            R5 → R6 → R7
-/
-- BEGIN SPEC
theorem Z_mul {ι ι' : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace ι] [MeasurableSpace ι']
    [MeasurableSingletonClass ι] [MeasurableSingletonClass ι']
    (𝓒 : CanonicalEnsemble ι) (𝓒' : CanonicalEnsemble ι') [𝓒.IsFinite] [𝓒'.IsFinite]
    (T : Temperature) :
    (𝓒 + 𝓒').partitionFunction T = 𝓒.partitionFunction T * 𝓒'.partitionFunction T :=
-- END SPEC
  by
    rw [partitionFunction_of_fintype, partitionFunction_of_fintype, partitionFunction_of_fintype,
      Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [energy_add_apply, mul_add, Real.exp_add]

theorem prob_mul {ι ι' : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace ι] [MeasurableSpace ι']
    [MeasurableSingletonClass ι] [MeasurableSingletonClass ι']
    (𝓒 : CanonicalEnsemble ι) (𝓒' : CanonicalEnsemble ι') [𝓒.IsFinite] [𝓒'.IsFinite]
    (T : Temperature) (i : ι) (j : ι') :
    (𝓒 + 𝓒').probability T (i, j) = 𝓒.probability T i * 𝓒'.probability T j := by
  simp only [probability, mathematicalPartitionFunction_of_fintype, Fintype.sum_prod_type,
    energy_add_apply, mul_add, Real.exp_add, ← Finset.sum_mul_sum, div_mul_div_comm]

/- SKELETON · U_add
  MILESTONE (prove first, as a separate lemma above `U_add`, binders of `Z_mul` plus `(i : ι) (j : ι')`):
       (𝓒 + 𝓒').probability T (i, j) = 𝓒.probability T i * 𝓒'.probability T j
     one `simp only [...]` with, in this order:                  R8, R9, R2, R5, R6, R7, ← R3, R10
  1. Each `meanEnergy` → its finite sum (3×), then the left sum → a double sum:  R11 ×3, R2
  2. Inside the double sum: `simp only` with the MILESTONE and R5, then split
     `(E i + E' j) * (p i * p' j)` into two double sums:                        R12, R13
  3. The two normalisations `h1 : ∑ i, 𝓒.probability T i = 1` and `h2` (for 𝓒'): R14, R14
  4. Split the `+` into two goals, focus each with `·`:                          R15
  5. Goal 1 (energy on the OUTER index):                       R16 → R17 → simp only [h2] → R18
  6. Goal 2 (energy on the INNER index): swap the sums, move `𝓒.probability T _`
     to the end of each product, then as goal 1 with `h1`:      R19 → R20 → R16 → R17 → h1 → R18
-/
-- BEGIN SPEC
theorem U_add {ι ι' : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace ι] [MeasurableSpace ι']
    [MeasurableSingletonClass ι] [MeasurableSingletonClass ι'] [Nonempty ι] [Nonempty ι']
    (𝓒 : CanonicalEnsemble ι) (𝓒' : CanonicalEnsemble ι') [𝓒.IsFinite] [𝓒'.IsFinite]
    (T : Temperature) :
    (𝓒 + 𝓒').meanEnergy T = 𝓒.meanEnergy T + 𝓒'.meanEnergy T :=
-- END SPEC
  by
    rw [meanEnergy_of_fintype, meanEnergy_of_fintype, meanEnergy_of_fintype, Fintype.sum_prod_type]
    simp only [prob_mul, energy_add_apply, add_mul, Finset.sum_add_distrib]
    have h1 := sum_probability_eq_one 𝓒 T
    have h2 := sum_probability_eq_one 𝓒' T
    congr 1
    · simp only [← mul_assoc, ← Finset.mul_sum, h2, mul_one]
    · rw [Finset.sum_comm]
      simp only [mul_comm (𝓒.probability T _), ← mul_assoc, ← Finset.mul_sum, h1, mul_one]

end M173

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every quantity has an `_of_fintype` formula that makes it a finite sum (R1, R9, R11), and a sum over
    the product space `ι × ι'` is a double sum (R2). Then it is algebra on double sums.
H2. `Z_mul`: write the right side as a double sum too (R3), compare summand by summand with
    `Finset.sum_congr` (R4) and factor `exp (-β (E i + E' j)) = exp (-β E i) * exp (-β E' j)` (R5–R7).
    Helper: unfold `probability`; numerator and denominator factor the same way, then `div_mul_div_comm`.
    `U_add`: after the helper, `(E i + E' j) p i p' j` splits into two double sums (R12, R13); `congr 1`
    separates them, and each collapses via `∑ p = 1` (R14), the second after swapping the sums (R19).
H3. `Z_mul`: `rw [partitionFunction_of_fintype, partitionFunction_of_fintype, partitionFunction_of_fintype,
    Fintype.sum_prod_type, Finset.sum_mul_sum]`, then
    `refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_`.
    Helper: `simp only [probability, mathematicalPartitionFunction_of_fintype, Fintype.sum_prod_type,
    energy_add_apply, mul_add, Real.exp_add, ← Finset.sum_mul_sum, div_mul_div_comm]`.
    `U_add`, goal 1 after `congr 1`: `simp only [← mul_assoc, ← Finset.mul_sum, h2, mul_one]`.
-/

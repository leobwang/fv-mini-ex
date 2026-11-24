/- M152 | Mean energy lies in the spectrum's range | 10 min | meanEnergyBetaReal, Finset.sum_le_sum, calc, physlib
GOAL
  If every energy level satisfies `m ≤ E i ≤ M`, then the thermal mean energy
  `U(b) = ∑ i, E i * p i` (with Boltzmann weights `p i = exp (-b E i) / Z(b)`, kB = 1) also lies in
  `[m, M]`, at every inverse temperature `b`, including negative ones.

REFERENCE
  #check CanonicalEnsemble.meanEnergyBetaReal   -- 𝓒.meanEnergyBetaReal b = ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i
  #check CanonicalEnsemble.probabilityBetaReal  -- 𝓒.probabilityBetaReal b i = exp (-b * 𝓒.energy i) / Z(b)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  #check Finset.sum_le_sum  -- (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
  #check Finset.mul_sum     -- a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
  #check mul_le_mul_of_nonneg_right  -- b ≤ c → 0 ≤ a → b * a ≤ c * a
  `calc a = b := h1` with `_ ≤ c := h2` on the next line chains `=` and `≤` into `a ≤ c`.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M152

-- BEGIN SPEC
theorem meanEnergy_bounds {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b m M : ℝ) (hm : ∀ i, m ≤ 𝓒.energy i) (hM : ∀ i, 𝓒.energy i ≤ M) :
    m ≤ 𝓒.meanEnergyBetaReal b ∧ 𝓒.meanEnergyBetaReal b ≤ M :=
-- END SPEC
  by
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
    have hp : ∀ i, 0 ≤ 𝓒.probabilityBetaReal b i := fun i => by
      unfold probabilityBetaReal; positivity
    have h1 : ∑ i, 𝓒.probabilityBetaReal b i = 1 := by
      simp only [probabilityBetaReal, ← Finset.sum_div]
      exact div_self hZ.ne'
    unfold meanEnergyBetaReal
    constructor
    · calc m = ∑ i, m * 𝓒.probabilityBetaReal b i := by rw [← Finset.mul_sum, h1, mul_one]
        _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (hp i)
    · calc _ ≤ ∑ i, M * 𝓒.probabilityBetaReal b i :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hM i) (hp i)
        _ = M := by rw [← Finset.mul_sum, h1, mul_one]

end M152

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A weighted average of numbers in `[m, M]` with non-negative weights summing to 1 stays in `[m, M]`.
H2. First prove `hp : ∀ i, 0 ≤ p i` and `h1 : ∑ i, p i = 1` (the facts of M150). Then write `m` as
    `∑ i, m * p i` and compare the sums term by term.
H3. `calc m = ∑ i, m * 𝓒.probabilityBetaReal b i := by rw [← Finset.mul_sum, h1, mul_one]`
    `_ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (hp i)`; mirror it for `M`.
-/

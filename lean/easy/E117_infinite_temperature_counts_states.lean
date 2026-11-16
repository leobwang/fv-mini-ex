/- E117 | Infinite temperature counts states | 2-3 min | mathematicalPartitionFunctionBetaReal, Finset.sum_const, simp, physlib
GOAL
  `𝓒.mathematicalPartitionFunctionBetaReal b` is `Z(β) = ∑ i, e^{-β E_i}` over the finitely many states
  `i : ι` (units with k_B = 1, β a plain real). If every state has energy `E`, `Z = |ι| e^{-βE}`; and at
  `β = 0` (infinite temperature) every weight is 1, so `Z` counts the states.

REFERENCE
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- (𝓒) (b : ℝ) : ℝ,  := ∑ i, Real.exp (-b * 𝓒.energy i)
  #check Finset.sum_const   -- ∑ _x ∈ s, c = s.card • c
  #check Finset.card_univ   -- Finset.univ.card = Fintype.card α     (`∑ i, …` is a sum over `Finset.univ`)
  #check nsmul_eq_mul       -- n • a = ↑n * a
  `simp [f]` with a definition name `f` unfolds `f` while simplifying; `simp [h]` with a hypothesis
  `h : ∀ i, g i = c` uses it as a rewrite rule, also under a `∑`.
  `Fintype.card ι` is the number of elements of the finite type `ι`; here it is cast to ℝ.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble

namespace E117

-- BEGIN SPEC
theorem Z_degenerate {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)
    (E b : ℝ) (h : ∀ i, 𝓒.energy i = E) :
    𝓒.mathematicalPartitionFunctionBetaReal b = Fintype.card ι * Real.exp (-b * E) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem Z_at_beta_zero {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) :
    𝓒.mathematicalPartitionFunctionBetaReal 0 = Fintype.card ι :=
-- END SPEC
  sorry

end E117

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both goals are about a sum whose terms do not depend on `i` (once you know the energies or `b = 0`).
H2. Unfold the definition, rewrite each term to a constant, then a constant sum is `card • c`.
H3. `simp [mathematicalPartitionFunctionBetaReal, h]` for the first; for the second, the same `simp`
    without `h` (it uses `neg_zero`, `zero_mul`, `Real.exp_zero`, `Finset.sum_const`, `Finset.card_univ`).
-/

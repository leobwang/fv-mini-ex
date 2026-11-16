/- E116 | Two-state partition function | 2-3 min | CanonicalEnsemble, twoState, partitionFunction, Fin.sum_univ_two, physlib
GOAL
  physlib's `twoState E₀ E₁ : CanonicalEnsemble (Fin 2)` is a two-level system: state `0` has energy
  `E₀`, state `1` has energy `E₁`. With energies `0` and `ε`, show `Z = 1 + e^{-βε}`.

REFERENCE
  #check CanonicalEnsemble.partitionFunction_of_fintype  -- 𝓒.partitionFunction T = ∑ i, Real.exp (-↑T.β * 𝓒.energy i)
  #check CanonicalEnsemble.twoState_energy_fst  -- (twoState E₀ E₁).energy 0 = E₀    (and `_snd`: energy 1 = E₁)
  #check Fin.sum_univ_two   -- ∑ i, f i = f 0 + f 1    (a sum over `Fin 2`)
  #check Real.exp_zero      -- Real.exp 0 = 1
  `T.β : ℝ≥0` is the inverse temperature 1/(k_B T) and `↑T.β` its cast to ℝ. `partitionFunction_of_fintype`
  needs `[𝓒.IsFinite]` (finite states, counting measure); physlib's instance for `twoState` is found
  automatically, so never name it.
BANNED: twoState_partitionFunction_apply, twoState_partitionFunction_apply_eq_cosh
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble

namespace E116

-- BEGIN SPEC
theorem twoState_Z (ε : ℝ) (T : Temperature) :
    (twoState 0 ε).partitionFunction T = 1 + Real.exp (-(T.β : ℝ) * ε) :=
-- END SPEC
  by
    rw [partitionFunction_of_fintype, Fin.sum_univ_two, twoState_energy_fst, twoState_energy_snd,
      mul_zero, Real.exp_zero]

end E116

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `partitionFunction` is defined through an integral; `partitionFunction_of_fintype` turns it into a finite sum.
H2. After that rewrite, expand the sum over `Fin 2` and plug in the two energies.
H3. `rw [partitionFunction_of_fintype, Fin.sum_univ_two, twoState_energy_fst, twoState_energy_snd]`,
    then `mul_zero` and `Real.exp_zero` (or just `simp`).
-/

/- M157 | N independent spins | 5-10 min | nsmul, partitionFunction_nsmul, helmholtzFreeEnergy, physlib
GOAL
  `nsmul N 𝓒` is `N` distinguishable, non-interacting copies of `𝓒`. For `N` spins in a field `h`, each
  the two-level system `twoState (-h) h` (energies `-h`, `+h`), show `Z = (2 cosh (β h))^N` and
  `F = -N kB T log (2 cosh (β h))`, where `β = 1 / (kB T)`.

REFERENCE
  #check CanonicalEnsemble.partitionFunction_nsmul  -- (nsmul n 𝓒).partitionFunction T = 𝓒.partitionFunction T ^ n
  #check CanonicalEnsemble.partitionFunction_of_fintype  -- finite 𝓒: Z(T) = ∑ i, exp (-↑T.β * 𝓒.energy i)
  #check CanonicalEnsemble.helmholtzFreeEnergy  -- definition: F(T) = -kB * ↑T.val * log (𝓒.partitionFunction T)
  #check Fin.sum_univ_two  -- ∑ i : Fin 2, f i = f 0 + f 1   (`twoState E₀ E₁` has E 0 = E₀, E 1 = E₁)
  #check Real.cosh_eq      -- cosh x = (exp x + exp (-x)) / 2
  #check Real.log_pow      -- log (x ^ n) = n * log x
  `T.β : ℝ≥0` (ℝ≥0 = NNReal, the nonnegative reals) is β; `(T.β : ℝ)` casts it to ℝ. `rw [helmholtzFreeEnergy]` unfolds the definition, and
  a proved theorem (here `paramagnet_Z`) can be used in a later `rw`.
BANNED: helmholtzFreeEnergy_nsmul, twoState_partitionFunction_apply_eq_cosh, twoState_helmholtzFreeEnergy_eq, twoState_helmholtzFreeEnergy_eq_T_neq_zero, try?
NOTE: `(T.val : ℝ) = T.toReal` holds by `rfl`, and `Temperature.β_toReal : (T.β : ℝ) = 1 / (kB * T.toReal)`.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Constants Real

namespace M157

-- BEGIN SPEC
theorem paramagnet_Z (h : ℝ) (N : ℕ) (T : Temperature) :
    (nsmul N (twoState (-h) h)).partitionFunction T = (2 * Real.cosh ((T.β : ℝ) * h)) ^ N :=
-- END SPEC
  by
    rw [partitionFunction_nsmul, partitionFunction_of_fintype]
    simp [Fin.sum_univ_two, Real.cosh_eq]
    ring_nf

-- BEGIN SPEC
theorem paramagnet_F (h : ℝ) (N : ℕ) (T : Temperature) :
    (nsmul N (twoState (-h) h)).helmholtzFreeEnergy T =
      -N * kB * T.val * Real.log (2 * Real.cosh ((T.β : ℝ) * h)) :=
-- END SPEC
  by
    rw [helmholtzFreeEnergy, paramagnet_Z, Real.log_pow]
    ring

end M157

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Independence means the `N`-copy partition function is the single-spin one to the `N`th power;
    then only one spin's `Z = e^{βh} + e^{-βh}` has to be matched with `2 cosh (βh)`.
H2. `paramagnet_Z`: `rw [partitionFunction_nsmul, partitionFunction_of_fintype]`, expand the `Fin 2`
    sum and `cosh`, and tidy up. `paramagnet_F`: unfold `F`, reuse `paramagnet_Z`, pull the power out of the log.
H3. For Z, after expanding: `exp (βh) + exp (-βh) = 2 cosh (βh)` is `Real.cosh_eq` read backwards (`ring_nf`
    tidies the leftovers). For F, `Real.log_pow` pulls `N` out of the log; the rest is `ring`.
-/

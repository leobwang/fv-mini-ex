/- M161 | Entropy of a two-level system | 15-20 min | thermodynamicEntropy, shannonEntropy, Real.log_div, generalize, physlib
GOAL
  Compute the entropy of physlib's two-level system `twoState 0 ε` (energies `0` and `ε`) at temperature
  `T`, with `β = 1 / (kB T)`: `S = kB (log (1 + e^{-βε}) + βε / (e^{βε} + 1))`. physlib only states this
  as an `informal_lemma`; prove it.

REFERENCE
  #check CanonicalEnsemble.thermodynamicEntropy_eq_shannonEntropy  -- finite 𝓒: 𝓒.thermodynamicEntropy T = 𝓒.shannonEntropy T
  #check CanonicalEnsemble.shannonEntropy  -- definition: -kB * ∑ i, 𝓒.probability T i * log (𝓒.probability T i)
  #check CanonicalEnsemble.probability     -- definition: 𝓒.probability T i = exp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T
  #check CanonicalEnsemble.mathematicalPartitionFunction_of_fintype  -- finite 𝓒: Z(T) = ∑ i, exp (-↑T.β * 𝓒.energy i)
  #check Fin.sum_univ_two  -- ∑ i : Fin 2, f i = f 0 + f 1   (`twoState E₀ E₁` has E 0 = E₀, E 1 = E₁)
  #check Real.log_div      -- x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y
  #check Real.log_exp      -- log (exp x) = x
  example (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b := div_eq_div_iff hb hd
  example (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  `generalize (T.β : ℝ) * ε = x` replaces that term everywhere by a fresh variable `x`.
BANNED: twoState_probability_fst, twoState_probability_snd, twoState_helmholtzFreeEnergy_eq, twoState_helmholtzFreeEnergy_eq_T_neq_zero, twoState_meanEnergy_eq
NOTE: simp writes `-(β*ε)` but the spec has `-β*ε`; rewrite one into the other (`by ring`) before `generalize`,
  or `generalize` misses some occurrences.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Constants Real

namespace M161

-- BEGIN SPEC
theorem twoState_entropy (ε : ℝ) (T : Temperature) :
    (twoState 0 ε).thermodynamicEntropy T =
      kB * (Real.log (1 + Real.exp (-(T.β : ℝ) * ε)) +
        (T.β : ℝ) * ε / (Real.exp ((T.β : ℝ) * ε) + 1)) :=
-- END SPEC
  sorry

end M161

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Switch to the finite formula `S = -kB ∑ p log p`, compute the two Boltzmann probabilities, and then
    it is pure algebra in one variable `x = βε`.
H2. `rw [thermodynamicEntropy_eq_shannonEntropy, shannonEntropy]`. Prove
    `p 0 = 1 / (1 + exp (-(β ε)))` and `p 1 = exp (-(β ε)) / (1 + exp (-(β ε)))`, each by one
    `simp [probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two]`. Rewrite with them,
    then `generalize`. Use `generalize`, not `set`: `ring` treats a `set` variable and its unfolded term as different.
H3. With `D = 1 + exp (-x) > 0`: `rw [Real.log_div _ D.ne', Real.log_div _ D.ne', Real.log_one, Real.log_exp]`,
    rewrite `x / (exp x + 1) = x * exp (-x) / D` (via `div_eq_div_iff` and `linear_combination`), then `field_simp; ring`.
-/

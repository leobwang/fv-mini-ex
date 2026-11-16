/- M156 | Two-level system freezes out | 10-15 min | Filter.atTop, Tendsto, exp limits, physlib
GOAL
  physlib's `twoState 0 ε` is a two-level system with energies `0` (ground) and `ε > 0` (excited).
  Show that its mean energy `U(b) = ∑ i, E i * p i(b)` tends to the ground-state energy `0` as the
  inverse temperature `b → ∞`, i.e. as `T → 0` (units with kB = 1).

REFERENCE
  #check CanonicalEnsemble.meanEnergyBetaReal   -- U(b) = ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i
  #check CanonicalEnsemble.probabilityBetaReal  -- p b i = exp (-b * E i) / Z(b),  Z(b) = ∑ i, exp (-b * E i)
  #check Fin.sum_univ_two        -- ∑ i : Fin 2, f i = f 0 + f 1   (`twoState E₀ E₁` has E 0 = E₀, E 1 = E₁)
  #check Real.tendsto_exp_atTop  -- Tendsto exp atTop atTop
  #check Tendsto.atTop_mul_const -- 0 < r → Tendsto f l atTop → Tendsto (fun x => f x * r) l atTop
  #check Tendsto.atTop_add       -- f → ∞ and g → C give f + g → ∞
  #check Tendsto.div_atTop       -- f → a and g → ∞ give f / g → 0
  example : Tendsto (fun b : ℝ => b) atTop atTop := tendsto_id  -- `hg.comp hf`: limit of g ∘ f
  `Tendsto f atTop (𝓝 L)` reads "f b → L as b → ∞"; `𝓝 L` is the filter of neighbourhoods of L.
NOTE: `rw`/`simp_rw` with `h : ∀ b, U b = …` cannot rewrite the bare function `U`; use `funext h`.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Real Filter Topology

namespace M156

-- BEGIN SPEC
theorem twoState_low_T (ε : ℝ) (hε : 0 < ε) :
    Tendsto (twoState 0 ε).meanEnergyBetaReal atTop (𝓝 0) :=
-- END SPEC
  sorry

end M156

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Find a closed form first: the ground level has energy 0, so only the excited level contributes,
    `U(b) = ε e^{-bε} / (1 + e^{-bε}) = ε / (e^{bε} + 1)`. A constant over something that grows without
    bound tends to 0.
H2. `have h : ∀ b, (twoState 0 ε).meanEnergyBetaReal b = ε / (Real.exp (b * ε) + 1)`: unfold with
    `simp [meanEnergyBetaReal, probabilityBetaReal, mathematicalPartitionFunctionBetaReal, Fin.sum_univ_two]`,
    then `rw [Real.exp_neg]` and `field_simp`. Swap the function via `show … = fun b => … from funext h`.
H3. `apply Tendsto.div_atTop tendsto_const_nhds` leaves the denominator; build it as
    `(Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hε)).atTop_add tendsto_const_nhds`.
-/

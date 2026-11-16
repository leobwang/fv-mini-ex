/- H089 | Heat capacity as an energy variance | 1-1.5 h | HasDerivAt, quotient rule, variance, Antitone, physlib
GOAL
  For a finite system `𝓒` (units kB = 1) at inverse temperature `b`, write `E i = 𝓒.energy i`,
  `Z(b) = ∑ i, exp (-b E i)`, `p b i = exp (-b E i) / Z(b)` (the Boltzmann probability) and
  `U(b) = ∑ i, E i * p b i` (the mean energy). Derive by hand that `dU/db = -Var_b(E)`, where
  `Var_b(E) = ∑ i, p b i * (E i - U b)²` is the energy variance.
  Conclude that `U` decreases in `b` (so it increases with temperature: heat capacity `C ≥ 0`).

REFERENCE
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.probabilityBetaReal  -- p b i = exp (-b * 𝓒.energy i) / Z(b)
  #check CanonicalEnsemble.meanEnergyBetaReal   -- U(b) = ∑ i, 𝓒.energy i * p b i
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  #check HasDerivAt.fun_sum  -- (∀ i ∈ u, HasDerivAt (A i) (A' i) x) → HasDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x
  #check HasDerivAt.div      -- HasDerivAt c c' x → HasDerivAt d d' x → d x ≠ 0 → HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x
  #check HasDerivAt.congr_deriv  -- HasDerivAt f f' x → f' = g' → HasDerivAt f g' x
  example (b c : ℝ) : HasDerivAt (fun x => Real.exp (-x * c)) (Real.exp (-b * c) * (-1 * c)) b := ((hasDerivAt_id' b).neg.mul_const c).exp
  #check antitone_of_deriv_nonpos  -- Differentiable ℝ f → (∀ x, deriv f x ≤ 0) → Antitone f
  #check HasDerivAt.deriv    -- HasDerivAt f f' x → deriv f x = f'   (and `.differentiableAt`)
  `generalize 𝓒.mathematicalPartitionFunctionBetaReal b = Z at *` turns a big term into a fresh variable `Z`.
BANNED: deriv_meanEnergyBetaReal, deriv_meanEnergyNumerator, deriv_mathematicalPartitionFunctionBetaReal, derivWithin_meanEnergy_Beta_eq_neg_variance, fluctuation_dissipation_theorem_finite, fluctuation_dissipation_energy_parametric, differentiable_meanEnergyBetaReal, differentiable_meanEnergyNumerator, differentiable_mathematicalPartitionFunctionBetaReal, meanEnergy_eq_neg_deriv_log_mathZ_of_beta, meanEnergy_eq_neg_deriv_log_Z_of_beta, try?
NOTE: physlib proves this with `deriv`; it is banned here: the exercise is the `HasDerivAt` plumbing.
  `try?` is banned only because it runs for many minutes here.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace H089

section Milestones

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

-- MILESTONE (optional: change or delete)
theorem hasDerivAt_Z (b : ℝ) :
    HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal
      (-∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b := by
  unfold mathematicalPartitionFunctionBetaReal
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro i _
  -- WHY: `congr_deriv`, not `convert … using 1`, which leaves an instance-equality side goal.
  exact (((hasDerivAt_id' b).neg.mul_const (𝓒.energy i)).exp).congr_deriv (by simp; ring)

-- MILESTONE (optional: change or delete)
theorem hasDerivAt_N (b : ℝ) :
    HasDerivAt (fun x => ∑ i, 𝓒.energy i * Real.exp (-x * 𝓒.energy i))
      (-∑ i, 𝓒.energy i ^ 2 * Real.exp (-b * 𝓒.energy i)) b := by
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro i _
  exact ((((hasDerivAt_id' b).neg.mul_const (𝓒.energy i)).exp).const_mul (𝓒.energy i)).congr_deriv
    (by simp; ring)

-- MILESTONE (optional: change or delete)
theorem meanEnergy_eq_div :
    𝓒.meanEnergyBetaReal = fun x =>
      (∑ i, 𝓒.energy i * Real.exp (-x * 𝓒.energy i)) / 𝓒.mathematicalPartitionFunctionBetaReal x := by
  funext x
  simp only [meanEnergyBetaReal, probabilityBetaReal, Finset.sum_div, mul_div_assoc]

-- MILESTONE (optional: change or delete)
theorem variance_eq [Nonempty ι] (b : ℝ) :
    ∑ i, 𝓒.probabilityBetaReal b i * (𝓒.energy i - 𝓒.meanEnergyBetaReal b) ^ 2 =
      (∑ i, 𝓒.energy i ^ 2 * Real.exp (-b * 𝓒.energy i)) / 𝓒.mathematicalPartitionFunctionBetaReal b
        - 𝓒.meanEnergyBetaReal b ^ 2 := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
  have expand : ∀ (U Z w E : ℝ), w / Z * (E - U) ^ 2 =
      E ^ 2 * w / Z - 2 * U * (E * w) / Z + U ^ 2 * (w / Z) := by
    intro U Z w E; ring
  have hZsum : ∑ i, Real.exp (-b * 𝓒.energy i) = 𝓒.mathematicalPartitionFunctionBetaReal b := rfl
  simp only [probabilityBetaReal, expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.mul_sum, hZsum]
  simp only [meanEnergy_eq_div 𝓒]
  -- WHY: name the three sums first; `field_simp` would otherwise rewrite inside them.
  generalize 𝓒.mathematicalPartitionFunctionBetaReal b = Z at *
  generalize ∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i) = N
  generalize ∑ i, 𝓒.energy i ^ 2 * Real.exp (-b * 𝓒.energy i) = S2
  field_simp
  ring

end Milestones

-- BEGIN SPEC
theorem hasDerivAt_meanEnergy {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) :
    HasDerivAt 𝓒.meanEnergyBetaReal
      (-∑ i, 𝓒.probabilityBetaReal b i * (𝓒.energy i - 𝓒.meanEnergyBetaReal b) ^ 2) b :=
-- END SPEC
  by
    have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b
    rw [variance_eq, meanEnergy_eq_div 𝓒]
    refine ((hasDerivAt_N 𝓒 b).div (hasDerivAt_Z 𝓒 b) hZ.ne').congr_deriv ?_
    beta_reduce
    generalize 𝓒.mathematicalPartitionFunctionBetaReal b = Z at *
    generalize ∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i) = N
    generalize ∑ i, 𝓒.energy i ^ 2 * Real.exp (-b * 𝓒.energy i) = S2
    field_simp
    ring

-- BEGIN SPEC
theorem meanEnergy_antitone {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) : Antitone 𝓒.meanEnergyBetaReal :=
-- END SPEC
  by
    apply antitone_of_deriv_nonpos
    · intro b
      exact (hasDerivAt_meanEnergy 𝓒 b).differentiableAt
    · intro b
      rw [(hasDerivAt_meanEnergy 𝓒 b).deriv, neg_nonpos]
      refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (sq_nonneg _)
      exact (div_pos (exp_pos _) (𝓒.mathematicalPartitionFunctionBetaReal_pos b)).le

end H089

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `U = N / Z` with `N(x) = ∑ i, E i * exp (-x E i)`. Differentiate `Z` and `N` term by term
    (`Z' = -N`, `N' = -S₂` with `S₂ = ∑ i, E i² exp (-b E i)`), then use the quotient rule.
    For the variance, expand the square: `∑ p (E - U)² = ∑ p E² - 2U ∑ p E + U² ∑ p = S₂/Z - U²`.
H2. Main: rewrite the variance with `variance_eq` and `U` with `meanEnergy_eq_div`, then apply the quotient
    rule `HasDerivAt.div` to `hasDerivAt_N` and `hasDerivAt_Z`. It needs `Z b ≠ 0`: from
    `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` (so `hZ : 0 < Z b`) take `hZ.ne'`.
    The quotient-rule derivative differs from the goal's only by algebra in `Z`, `N`, `S₂`: fix it with
    `HasDerivAt.congr_deriv`.
    Antitone: `antitone_of_deriv_nonpos`, rewrite `deriv` with `(hasDerivAt_meanEnergy 𝓒 b).deriv`,
    and the variance is a sum of non-negative terms (`Finset.sum_nonneg`, `mul_nonneg`, `sq_nonneg`).
H3. Main: `refine ((hasDerivAt_N 𝓒 b).div (hasDerivAt_Z 𝓒 b) hZ.ne').congr_deriv ?_`, then `beta_reduce`.
    Key trick (also for `variance_eq`): `generalize` `Z`, `N` and `S₂` to fresh variables *before*
    `field_simp; ring`; otherwise `field_simp` rewrites inside the sums and the two sides stop matching.
    Term of `N`: `.const_mul (𝓒.energy i)` on the REFERENCE `exp` example, under
    `rw [← Finset.sum_neg_distrib]; apply HasDerivAt.fun_sum`.
-/

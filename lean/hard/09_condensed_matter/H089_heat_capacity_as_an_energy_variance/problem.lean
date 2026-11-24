/- H089 | Heat capacity as an energy variance | 1-1.5 h | HasDerivAt, quotient rule, variance, Antitone, physlib
GOAL
  For a finite system `𝓒` (units kB = 1) at inverse temperature `b`, write `E i = 𝓒.energy i`,
  `Z(b) = ∑ i, exp (-b E i)`, `p b i = exp (-b E i) / Z(b)` (the Boltzmann probability) and
  `U(b) = ∑ i, E i * p b i` (the mean energy). Derive by hand that `dU/db = -Var_b(E)`, where
  `Var_b(E) = ∑ i, p b i * (E i - U b)²` is the energy variance.
  Conclude that `U` decreases in `b` (so it increases with temperature: heat capacity `C ≥ 0`).
BANNED: deriv_meanEnergyBetaReal, deriv_meanEnergyNumerator, deriv_mathematicalPartitionFunctionBetaReal, derivWithin_meanEnergy_Beta_eq_neg_variance, fluctuation_dissipation_theorem_finite, fluctuation_dissipation_energy_parametric, differentiable_meanEnergyBetaReal, differentiable_meanEnergyNumerator, differentiable_mathematicalPartitionFunctionBetaReal, meanEnergy_eq_neg_deriv_log_mathZ_of_beta, meanEnergy_eq_neg_deriv_log_Z_of_beta, try?

GUIDE
  Entries R1–R36: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace H089

section Milestones

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

/- SKELETON · hasDerivAt_Z   (milestone 1: Z' = -N; used in hasDerivAt_meanEnergy)
  1. Unfold `Z` into its sum:                                                R1
  2. Push the outer `-` into the sum:                                        R2 (right to left)
  3. Differentiate term by term, then `intro i _`:                           R3
  4. Build the term's derivative from the identity: id → negate →
     times `𝓒.energy i` → exp; it is right up to algebra, so fix it:         R4 → R5 → R6 → R7, R8
  5. The algebra goal `f' = g'`:                                             R9 (`simp`), then `ring`
-/
-- MILESTONE (optional: change or delete)
theorem hasDerivAt_Z (b : ℝ) :
    HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal
      (-∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b := by
  sorry

/- SKELETON · hasDerivAt_N   (milestone 2: N' = -S₂; used in hasDerivAt_meanEnergy)
  1. Push the outer `-` into the sum, differentiate term by term, `intro i _`: R2, R3
  2. The term is `𝓒.energy i * exp (…)`: the chain of milestone 1, then the
     constant factor in front, then fix the form:                            R4 → R5 → R6 → R7 → R10, R8
  3. The algebra goal:                                                       R9 (`simp`), then `ring`
-/
-- MILESTONE (optional: change or delete)
theorem hasDerivAt_N (b : ℝ) :
    HasDerivAt (fun x => ∑ i, 𝓒.energy i * Real.exp (-x * 𝓒.energy i))
      (-∑ i, 𝓒.energy i ^ 2 * Real.exp (-b * 𝓒.energy i)) b := by
  sorry

/- SKELETON · meanEnergy_eq_div   (milestone 3: U = N / Z; used in variance_eq and hasDerivAt_meanEnergy)
  1. Equation of functions → equation at a point `x`:                        R11
  2. One `simp only` that unfolds `U` and `p` and moves `/ Z x` out of the
     sum on one side and into it on the other; it closes the goal:           R12, R13, R14
-/
-- MILESTONE (optional: change or delete)
theorem meanEnergy_eq_div :
    𝓒.meanEnergyBetaReal = fun x =>
      (∑ i, 𝓒.energy i * Real.exp (-x * 𝓒.energy i)) / 𝓒.mathematicalPartitionFunctionBetaReal x := by
  sorry

/- SKELETON · variance_eq   (milestone 4: Var = S₂/Z - U²; used in hasDerivAt_meanEnergy)
  1. `hZ : 0 < Z b`:                                                         R15
  2. Two facts for the `simp only` of step 3:                                have, R20
       expand : ∀ (U Z w E : ℝ), w / Z * (E - U) ^ 2 =
                  E ^ 2 * w / Z - 2 * U * (E * w) / Z + U ^ 2 * (w / Z)   (intro, then ring)
       hZsum  : ∑ i, Real.exp (-b * 𝓒.energy i) = 𝓒.mathematicalPartitionFunctionBetaReal b   (R20)
     The grouping in `expand` matters: every summand must end up as `(…) / Z`
     or `constant * (…)`, the shapes that R13 ← and R19 ← pull out of a sum.
  3. One `simp only`: unfold `p`; expand under `∑`; split the sums; pull
     `/ Z b` and the constant factors out; fold `∑ exp` into `Z b`:          R12, R16, R17, R18, R13 ←, R19 ←, R20
  4. Replace `U` by `N / Z`:                                                 milestone 3 with `simp only`
  5. Name `Z b` (`at *`, so `hZ` follows), then the sums `N b` and `S₂ b`:  R21 ×3
  6. Clear the denominators, then `ring`:                                    R22
-/
-- MILESTONE (optional: change or delete)
theorem variance_eq [Nonempty ι] (b : ℝ) :
    ∑ i, 𝓒.probabilityBetaReal b i * (𝓒.energy i - 𝓒.meanEnergyBetaReal b) ^ 2 =
      (∑ i, 𝓒.energy i ^ 2 * Real.exp (-b * 𝓒.energy i)) / 𝓒.mathematicalPartitionFunctionBetaReal b
        - 𝓒.meanEnergyBetaReal b ^ 2 := by
  sorry

end Milestones

/- SKELETON · hasDerivAt_meanEnergy
  Prove the four milestones above first; all four are used here.
  1. `hZ : 0 < Z b`:                                                         R15
  2. `rw` the goal's variance with milestone 4, then `U` with milestone 3:   rw [milestone 4, milestone 3]
  3. Quotient rule on milestone 2 (numerator `N`) and milestone 1 (`Z`),
     with `Z b ≠ 0`; the derivative is right up to algebra:                  R23, R24, R8
  4. Substitute the leftover `(fun x => N x / Z x) b`:                       R25
  5. Name `Z b` (`at *`), `N b`, `S₂ b`; clear denominators; `ring`:          R21 ×3, R22
-/
-- BEGIN SPEC
theorem hasDerivAt_meanEnergy {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) :
    HasDerivAt 𝓒.meanEnergyBetaReal
      (-∑ i, 𝓒.probabilityBetaReal b i * (𝓒.energy i - 𝓒.meanEnergyBetaReal b) ^ 2) b :=
-- END SPEC
  sorry

/- SKELETON · meanEnergy_antitone
  Uses hasDerivAt_meanEnergy (above) at every point `b`.
  1. Antitone ← differentiable and `deriv ≤ 0`; two goals, use bullets:     R26
  2. Differentiable: `intro b`, then from hasDerivAt_meanEnergy at `b`:      R27, R28
  3. `deriv ≤ 0`: `intro b`; `deriv` → `-Var`; `-a ≤ 0` → `0 ≤ a`:           R29, R30
  4. Var is a sum of `p b i * (…) ^ 2`: per term (`intro i _`), then split
     the product into two goals (bullets); the square is ≥ 0:               R31, R32, R33
  5. `0 ≤ p b i`: `p b i` is `exp (…) / Z b` by definition, so prove
     `0 < exp (…) / Z b` and weaken it:                                      R34 (R35, R15), R36
-/
-- BEGIN SPEC
theorem meanEnergy_antitone {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) : Antitone 𝓒.meanEnergyBetaReal :=
-- END SPEC
  sorry

end H089

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `U = N / Z` with `N(x) = ∑ i, E i * exp (-x E i)`. Differentiate `Z` and `N` term by term
    (`Z' = -N`, `N' = -S₂` with `S₂ = ∑ i, E i² exp (-b E i)`), then use the quotient rule.
    For the variance, expand the square: `∑ p (E - U)² = ∑ p E² - 2U ∑ p E + U² ∑ p = S₂/Z - U²`.
    The four milestones are exactly these steps; prove them first.
H2. Milestones 1, 2: `rw [← Finset.sum_neg_distrib]; apply HasDerivAt.fun_sum; intro i _` (R2, R3), then
    build each term from `hasDerivAt_id'` with `.neg`, `.mul_const`, `.exp` (and `.const_mul` for `N`), and
    fix the form with `.congr_deriv (by simp; ring)` (R4–R10).
    Main: rewrite with `variance_eq` and `meanEnergy_eq_div 𝓒`, apply the quotient rule `HasDerivAt.div` to
    `hasDerivAt_N` and `hasDerivAt_Z` with `hZ.ne'` (R23, R24), where
    `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` (R15); then `congr_deriv` for the algebra.
    Antitone: `antitone_of_deriv_nonpos` (R26), `(hasDerivAt_meanEnergy 𝓒 b).differentiableAt` and `.deriv`
    (R28, R29), `neg_nonpos`, then `Finset.sum_nonneg`, `mul_nonneg`, `sq_nonneg` (R30–R33).
H3. Main: `refine ((hasDerivAt_N 𝓒 b).div (hasDerivAt_Z 𝓒 b) hZ.ne').congr_deriv ?_`, then `beta_reduce`.
    Key trick (also for `variance_eq`): `generalize 𝓒.mathematicalPartitionFunctionBetaReal b = Z at *` and
    the same (without `at *`) for the sums `N b`, `S₂ b` *before* `field_simp; ring`; otherwise
    `field_simp` rewrites inside the sums and the two sides stop matching (R21, R22).
    Term of `N`: `((((hasDerivAt_id' b).neg.mul_const (𝓒.energy i)).exp).const_mul (𝓒.energy i)).congr_deriv
    (by simp; ring)`.
-/

/- H094 | Thermal quantum oscillator (Planck) | 1.5-2 h | CanonicalEnsemble on ℕ, counting measure, tsum, geometric series, physlib
GOAL
  `qho ε` is a quantum harmonic oscillator with level spacing `ε > 0`: states `n : ℕ` (counting measure),
  energies `E_n = ε (n + 1/2)`. With `β = 1 / (kB T)`, prove `Z = 1 / (2 sinh (βε/2))` and
  `⟨E⟩ = ε/2 + ε / (e^{βε} - 1)`: zero-point energy plus `ε` times the Planck (Bose) occupation.

GUIDE
  Entries R1–R43: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas

open CanonicalEnsemble Real MeasureTheory

namespace H094

-- BEGIN SPEC
/-- Quantum harmonic oscillator with level spacing `ε`: `E_n = ε (n + 1/2)`. -/
noncomputable def qho (ε : ℝ) : CanonicalEnsemble ℕ where
  energy n := ε * (n + 1 / 2)
  dof := 0
  μ := Measure.count
  energy_measurable := by fun_prop
-- END SPEC

/- SKELETON · weight_eq   (MILESTONE 1: used in both spec theorems to rewrite the Boltzmann weight)
  1. Fold the right side into one exponential: the power, then the product     R1, R2   (both `rw [← …]`)
  2. Unfold the energy of `qho ε`                                               R3
  3. Both sides are now `rexp (…)` of ring-equal arguments                      R4
-/
-- MILESTONE (optional: change or delete)
theorem weight_eq (ε β : ℝ) (n : ℕ) :
    Real.exp (-β * (qho ε).energy n) = Real.exp (-(β * ε) / 2) * Real.exp (-(β * ε)) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  simp only [qho]
  ring_nf

/- SKELETON · integral_count_eq_tsum   (MILESTONE 2: integral over ℕ → sum; used in both spec theorems)
  1. Integral → sum, leaving integrability as a `?_` goal:
       rw [integral_countable (integrable_count_iff.mpr ?_)]                   R5, R6
  2. Main goal: the point weight `count.real {x}` is 1                          R7
  3. The `?_` goal `Summable fun x => ‖f x‖`: from `hf.abs`, with ‖·‖ = |·|     R8, R9 inside R10
-/
-- MILESTONE (optional: change or delete)
theorem integral_count_eq_tsum {f : ℕ → ℝ} (hf : Summable f) :
    ∫ n, f n ∂(Measure.count : Measure ℕ) = ∑' n, f n := by
  rw [integral_countable (integrable_count_iff.mpr ?_)]
  · simp [Measure.real]
  · simpa [Real.norm_eq_abs] using hf.abs

/- SKELETON · tsum_weight   (MILESTONE 3: the series for Z; used in `qho_partitionFunction`)
  1. Fact `hr1 : Real.exp (-x) < 1`                                             R11, R12
  2. Pull the constant out of the sum                                           R14
  3. Sum the geometric series (its `0 ≤ r` from R13)                            R15
  4. `a * b⁻¹ = a / b` closes it                                                R16 (reversed: `.symm`)
-/
-- MILESTONE (optional: change or delete)
theorem tsum_weight (x : ℝ) (hx : 0 < x) :
    ∑' n : ℕ, Real.exp (-x / 2) * Real.exp (-x) ^ n = Real.exp (-x / 2) / (1 - Real.exp (-x)) := by
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr1]
  exact (div_eq_mul_inv _ _).symm

/- SKELETON · qho_partitionFunction
  Prove the three MILESTONES above first: steps 5 and 6 use them.
  1. `hβ : 0 < (T.β : ℝ)`                                                       R17
  2. Unfold Z:  R18 → R19, then `(qho ε).dof = 0` and the trivial power          R20 → R21
  3. Name `x = βε`; `hx0 : 0 < x` by `rw [← hx]` then                           R22, R23
  4. Facts: `hr1 : Real.exp (-x) < 1` (R11, R12) and
       `hsum : Summable fun n : ℕ => Real.exp (-x / 2) * Real.exp (-x) ^ n`    R24 (+ R13), R25
  5. `hw : ∀ n, <weight of n> = Real.exp (-x / 2) * Real.exp (-x) ^ n`  (weight_eq, `rw [hx]`);
     restate the goal with `∂Measure.count` (R26), then rewrite under `∫ n, …`  R27
  6. rw [integral_count_eq_tsum hsum, tsum_weight x hx0], then sinh             R28
  7. Algebra, with `c = Real.exp (-x / 2)`:
       `hcc : Real.exp (x / 2) * Real.exp (-x / 2) = 1`                        R2, ring_nf, R29
       `hrc : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2)`           R2, R4
       match the forms: rw [show -(x / 2) = -x / 2 by ring, hrc]               R30
       `0 < c`, `c < 1` (R13, R11), then name `c` everywhere                   R31
       `1 - c ^ 2 ≠ 0`, `Real.exp (x / 2) - c ≠ 0`                             R32
       clear denominators, finish with `hcc`                                    R33 → R34
-/
-- BEGIN SPEC
theorem qho_partitionFunction (ε : ℝ) (hε : 0 < ε) (T : Temperature) (hT : 0 < T.val) :
    (qho ε).partitionFunction T = 1 / (2 * Real.sinh ((T.β : ℝ) * ε / 2)) :=
-- END SPEC
  by
    have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT
    rw [partitionFunction_def, mathematicalPartitionFunction_eq_integral,
      show (qho ε).dof = 0 from rfl, pow_zero, div_one]
    generalize hx : (T.β : ℝ) * ε = x
    have hx0 : 0 < x := by rw [← hx]; positivity
    have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hsum : Summable fun n : ℕ => Real.exp (-x / 2) * Real.exp (-x) ^ n :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left _
    have hw : ∀ n, Real.exp (-(T.β : ℝ) * (qho ε).energy n) =
        Real.exp (-x / 2) * Real.exp (-x) ^ n := by
      intro n; rw [weight_eq, hx]
    show ∫ n, Real.exp (-(T.β : ℝ) * (qho ε).energy n) ∂Measure.count = _
    simp_rw [hw]
    rw [integral_count_eq_tsum hsum, tsum_weight x hx0, Real.sinh_eq]
    -- WHY: name `c = e^{-x/2}`; then `e^{-x} = c²` and `e^{x/2} c = 1` make it a rational identity in `c`.
    have hcc : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have hrc : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [show -(x / 2) = -x / 2 by ring, hrc]
    have hc1 : Real.exp (-x / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hc0 := Real.exp_pos (-x / 2)
    generalize Real.exp (-x / 2) = c at hcc hc0 hc1 ⊢
    have h1 : 1 - c ^ 2 ≠ 0 := by nlinarith
    have h2 : Real.exp (x / 2) - c ≠ 0 := by nlinarith [Real.exp_pos (x / 2)]
    field_simp
    linear_combination hcc

/- SKELETON · qho_meanEnergy
  Uses MILESTONES 1 and 2 (weight_eq, integral_count_eq_tsum).
  1. `hβ`                                                                       R17
  2. ⟨E⟩ → ratio of integrals (R35); restate both integrals with `∂Measure.count`  R26
  3. `hE : ∀ n : ℕ, (qho ε).energy n = ε * (n + 1 / 2)` (`rfl`); rewrite
     `weight_eq` and `hE` under the binders                                    R27
  4. Name `x = βε` and prove `0 < x`                                            R22, R23
  5. `set r := Real.exp (-x)`, `set c := Real.exp (-x / 2)`                     R36
  6. Facts: `0 ≤ r` (R13), `r < 1` (R11, R12), `‖r‖ < 1` (R9 → R37 → R38),
     `Summable fun n => r ^ n` (R24), `Summable fun n => (n : ℝ) * r ^ n`      R39
  7. Split the numerator term: `ε (n + 1/2) (c rⁿ) = ε c (n rⁿ) + (ε c / 2) rⁿ`  (`ring`), R27
  8. Both integrals → sums with `integral_count_eq_tsum` (summability: R25, R40);
     then split and evaluate:                                                  R41 → R14 (×3) → R42 → R15
  9. Facts: `0 < c` (R13), `0 < 1 - r` (R12), `hex : Real.exp x * r = 1`
     (`rw [hr]`, R2, `simp`), `0 < Real.exp x - 1`                              R43
 10. Clear denominators, then close with `hex`                                 R33 → R32 (`nlinarith [hex]`)
-/
-- BEGIN SPEC
theorem qho_meanEnergy (ε : ℝ) (hε : 0 < ε) (T : Temperature) (hT : 0 < T.val) :
    (qho ε).meanEnergy T = ε / 2 + ε / (Real.exp ((T.β : ℝ) * ε) - 1) :=
-- END SPEC
  by
    have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT
    rw [meanEnergy_eq_ratio_of_integrals]
    show (∫ n, (qho ε).energy n * Real.exp (-(T.β : ℝ) * (qho ε).energy n) ∂Measure.count) /
      (∫ n, Real.exp (-(T.β : ℝ) * (qho ε).energy n) ∂Measure.count) = _
    have hE : ∀ n : ℕ, (qho ε).energy n = ε * (n + 1 / 2) := fun n => rfl
    simp_rw [weight_eq, hE]
    generalize hx : (T.β : ℝ) * ε = x
    have hx0 : 0 < x := by rw [← hx]; positivity
    set r := Real.exp (-x) with hr
    set c := Real.exp (-x / 2) with hc
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hnr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
    have hs0 : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
    have hs1 : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnr
    have hnum : ∀ n : ℕ, ε * (n + 1 / 2) * (c * r ^ n) =
        ε * c * ((n : ℝ) * r ^ n) + ε * c / 2 * r ^ n := fun n => by ring
    simp_rw [hnum]
    rw [integral_count_eq_tsum ((hs1.mul_left _).add (hs0.mul_left _)),
      integral_count_eq_tsum (hs0.mul_left _), (hs1.mul_left _).tsum_add (hs0.mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_coe_mul_geometric_of_norm_lt_one hnr, tsum_geometric_of_lt_one hr0 hr1]
    have hcpos : 0 < c := Real.exp_pos _
    have h1r : 0 < 1 - r := by linarith
    have hex : Real.exp x * r = 1 := by rw [hr, ← Real.exp_add]; simp
    have hex1 : 0 < Real.exp x - 1 := by linarith [Real.add_one_lt_exp hx0.ne']
    field_simp
    nlinarith [hex]

end H094

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With `x = βε > 0`, `c = e^{-x/2}` and `r = e^{-x} < 1`, the Boltzmann weight is `c · rⁿ` (weight_eq), so
    both integrals over `ℕ` are geometric-type series: `Z = c / (1 - r)`, and the numerator of `⟨E⟩` is
    `ε c ∑ n rⁿ + (ε c / 2) ∑ rⁿ`. After that it is algebra with `e^{x} r = 1` and `r = c²`.
H2. Prove the milestones first; every `∫ · ∂count` becomes `∑'` through `integral_count_eq_tsum`, which needs a
    `Summable` fact you state beforehand (R24, R25, R39, R40). Unfold with R18 → R21 (Z) or R35 (⟨E⟩), change
    `∂(qho ε).μ` to `∂Measure.count` with `show` (R26), and rewrite the weight under the binder with `simp_rw`
    (R27). Name `x` (R22) and then `c`, `r` (R31 or R36) so `field_simp` (R33) sees a rational identity.
H3. Z, end: `generalize Real.exp (-x / 2) = c at hcc hc0 hc1 ⊢`, then `field_simp` and `linear_combination hcc`
    with `hcc : Real.exp (x / 2) * c = 1`. ⟨E⟩, middle: `rw [(hs1.mul_left _).tsum_add (hs0.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hnr,
    tsum_geometric_of_lt_one hr0 hr1]`; end: `field_simp` and `nlinarith [hex]` with `hex : Real.exp x * r = 1`.
-/

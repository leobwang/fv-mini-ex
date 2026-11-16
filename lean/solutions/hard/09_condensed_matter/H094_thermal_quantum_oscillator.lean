/- H094 | Thermal quantum oscillator (Planck) | 1.5-2 h | CanonicalEnsemble on ℕ, counting measure, tsum, geometric series, physlib
GOAL
  `qho ε` is a quantum harmonic oscillator with level spacing `ε > 0`: states `n : ℕ` (counting measure),
  energies `E_n = ε (n + 1/2)`. With `β = 1 / (kB T)`, prove `Z = 1 / (2 sinh (βε/2))` and
  `⟨E⟩ = ε/2 + ε / (e^{βε} - 1)`: zero-point energy plus `ε` times the Planck (Bose) occupation.

REFERENCE
  #check CanonicalEnsemble.partitionFunction_def  -- Z T = Z_math T / phaseSpaceunit ^ dof   (here `rw [show (qho ε).dof = 0 from rfl]`)
  #check CanonicalEnsemble.mathematicalPartitionFunction_eq_integral  -- Z_math T = ∫ i, exp (-↑T.β * E i) ∂𝓒.μ
  #check CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals  -- ⟨E⟩ = (∫ i, E i * exp (-↑T.β * E i) ∂𝓒.μ) / ∫ i, exp (…) ∂𝓒.μ
  #check MeasureTheory.integral_countable    -- Integrable f μ → ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x   (`μ.real {x}` = measure of `{x}` as a real; 1 for `Measure.count`)
  #check MeasureTheory.integrable_count_iff  -- Integrable f Measure.count ↔ Summable (fun x => ‖f x‖)
  #check tsum_geometric_of_lt_one  -- 0 ≤ r → r < 1 → ∑' n, r ^ n = (1 - r)⁻¹   (`summable_geometric_of_lt_one`: Summable)
  #check tsum_coe_mul_geometric_of_norm_lt_one   -- ‖r‖ < 1 → ∑' n, n * r ^ n = r / (1 - r) ^ 2
  #check summable_pow_mul_geometric_of_norm_lt_one  -- (k : ℕ) → ‖r‖ < 1 → Summable (fun n => n ^ k * r ^ n)
  #check Summable.tsum_add  -- Summable f → Summable g → ∑' (f + g) = ∑' f + ∑' g;  also `tsum_mul_left`, `Summable.mul_left`
  #check Real.exp_nat_mul   -- exp (n * x) = exp x ^ n
  #check Real.sinh_eq       -- sinh x = (exp x - exp (-x)) / 2
  `∑' n, f n` is the infinite sum (`tsum`); it equals the true sum only when `Summable f` (else it is 0).
NOTE: `(qho ε).μ = Measure.count` is `rfl`; `T.val`, `T.β : ℝ≥0` (nonnegative reals) and `↑T.β` = `(T.β : ℝ)`
  is the cast to ℝ; `Temperature.beta_pos : 0 < T.val → 0 < (T.β : ℝ)`.
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

-- MILESTONE (optional: change or delete)
theorem weight_eq (ε β : ℝ) (n : ℕ) :
    Real.exp (-β * (qho ε).energy n) = Real.exp (-(β * ε) / 2) * Real.exp (-(β * ε)) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  simp only [qho]
  ring_nf

-- MILESTONE (optional: change or delete)
theorem integral_count_eq_tsum {f : ℕ → ℝ} (hf : Summable f) :
    ∫ n, f n ∂(Measure.count : Measure ℕ) = ∑' n, f n := by
  rw [integral_countable (integrable_count_iff.mpr ?_)]
  · simp [Measure.real]
  · simpa [Real.norm_eq_abs] using hf.abs

-- MILESTONE (optional: change or delete)
theorem tsum_weight (x : ℝ) (hx : 0 < x) :
    ∑' n : ℕ, Real.exp (-x / 2) * Real.exp (-x) ^ n = Real.exp (-x / 2) / (1 - Real.exp (-x)) := by
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr1]
  exact (div_eq_mul_inv _ _).symm

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
H1. With `x = βε > 0`, `c = e^{-x/2}` and `r = e^{-x} < 1`, the Boltzmann weight is `c · rⁿ`, so both
    integrals over `ℕ` are geometric-type series: `Z = c / (1 - r)` and the numerator of `⟨E⟩` is
    `ε c (∑ n rⁿ) + (ε c / 2)(∑ rⁿ)`. Everything after that is algebra with `e^{x} r = 1`, `r = c²`.
H2. Turn `∫ · ∂count` into `∑'` with `integral_countable (integrable_count_iff.mpr _)`; the factor
    `count.real {n}` is 1 (`simp [Measure.real]`), and absolute summability comes from `hf.abs`. `Z`:
    `rw [partitionFunction_def, mathematicalPartitionFunction_eq_integral]`, then
    `rw [show (qho ε).dof = 0 from rfl, pow_zero, div_one]`, `weight_eq`, `integral_count_eq_tsum`, `tsum_weight`, `Real.sinh_eq`.
    `⟨E⟩`: `rw [meanEnergy_eq_ratio_of_integrals]` and write the numerator term as
    `ε c (n rⁿ) + ε c / 2 · rⁿ`.
H3. Name things with `generalize`/`set` (`set r := Real.exp (-x) with hr`) and state summability first:
    `summable_geometric_of_lt_one hr0 hr1` and, with `hnr : ‖r‖ < 1`,
    `by simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnr`.
    Numerator: `rw [(hs1.mul_left _).tsum_add (hs0.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one hnr, tsum_geometric_of_lt_one hr0 hr1]`, then `field_simp` and
    `nlinarith [hex]` with `hex : Real.exp x * r = 1`.
-/

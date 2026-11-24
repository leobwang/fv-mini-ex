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
  sorry

-- MILESTONE (optional: change or delete)
theorem integral_count_eq_tsum {f : ℕ → ℝ} (hf : Summable f) :
    ∫ n, f n ∂(Measure.count : Measure ℕ) = ∑' n, f n := by
  sorry

-- MILESTONE (optional: change or delete)
theorem tsum_weight (x : ℝ) (hx : 0 < x) :
    ∑' n : ℕ, Real.exp (-x / 2) * Real.exp (-x) ^ n = Real.exp (-x / 2) / (1 - Real.exp (-x)) := by
  sorry

-- BEGIN SPEC
theorem qho_partitionFunction (ε : ℝ) (hε : 0 < ε) (T : Temperature) (hT : 0 < T.val) :
    (qho ε).partitionFunction T = 1 / (2 * Real.sinh ((T.β : ℝ) * ε / 2)) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem qho_meanEnergy (ε : ℝ) (hε : 0 < ε) (T : Temperature) (hT : 0 < T.val) :
    (qho ε).meanEnergy T = ε / 2 + ε / (Real.exp ((T.β : ℝ) * ε) - 1) :=
-- END SPEC
  sorry

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

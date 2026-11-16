/- H093 | Equipartition | 1-1.5 h | Gaussian integrals, Gamma function, rpow, CanonicalEnsemble on ℝ, physlib
GOAL
  `harmonic κ` is one classical harmonic degree of freedom: states `x : ℝ` with Lebesgue measure and
  energy `E(x) = κ x² / 2` (`κ > 0` the stiffness). Prove equipartition: at temperature `T > 0` its mean
  energy is `kB T / 2`, where `⟨E⟩ = (∫ E e^{-βE} dx) / (∫ e^{-βE} dx)` and `β = 1 / (kB T)`.

REFERENCE
  #check CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals  -- 𝓒.meanEnergy T = (∫ i, E i * exp (-↑T.β * E i) ∂𝓒.μ) / ∫ i, exp (-↑T.β * E i) ∂𝓒.μ
  #check integral_gaussian      -- ∫ x : ℝ, exp (-b * x ^ 2) = √(π / b)
  #check integral_rpow_mul_exp_neg_mul_rpow  -- 0 < p → -1 < q → 0 < b → ∫ x in Ioi 0, x ^ q * exp (-b * x ^ p) = b ^ (-(q+1)/p) * (1/p) * Γ((q+1)/p)
  #check integral_comp_abs      -- ∫ x, f |x| = 2 * ∫ x in Set.Ioi 0, f x
  #check Real.Gamma_add_one     -- s ≠ 0 → Γ(s + 1) = s * Γ(s);   with `Real.Gamma_one_half_eq : Γ(1/2) = √π`
  #check Real.rpow_two          -- x ^ (2 : ℝ) = x ^ 2  (real power `rpow` vs. natural power)
  #check Real.rpow_add          -- 0 < x → x ^ (y + z) = x ^ y * x ^ z;  also `Real.rpow_neg`, `Real.sqrt_eq_rpow`
  #check integral_const_mul     -- ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
  #check Temperature.beta_pos   -- 0 < T.val → 0 < (T.β : ℝ)
  #check Constants.kB_pos       -- 0 < kB
  `(harmonic κ).μ = volume` and `(harmonic κ).energy x = κ * x ^ 2 / 2` hold by `rfl` (`simp only [harmonic]`).
NOTE: `T.val`, `T.β : ℝ≥0` (nonnegative reals); `↑T.β` = `(T.β : ℝ)` is the cast to ℝ. `(T.val : ℝ) = T.toReal`
  holds by `rfl`, and `Temperature.β_toReal : (T.β : ℝ) = 1 / (kB * T.toReal)`.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

open CanonicalEnsemble Constants Real MeasureTheory

namespace H093

-- BEGIN SPEC
/-- One classical harmonic degree of freedom with stiffness `κ`. -/
noncomputable def harmonic (κ : ℝ) : CanonicalEnsemble ℝ where
  energy x := κ * x ^ 2 / 2
  dof := 1
  energy_measurable := by fun_prop
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem moment2 (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-a * x ^ 2) = (1 / (2 * a)) * ∫ x : ℝ, Real.exp (-a * x ^ 2) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem weight_eq (κ β : ℝ) :
    (fun x : ℝ => Real.exp (-β * (harmonic κ).energy x)) =
      fun x => Real.exp (-(β * κ / 2) * x ^ 2) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem integrand_eq (κ β : ℝ) :
    (fun x : ℝ => (harmonic κ).energy x * Real.exp (-β * (harmonic κ).energy x)) =
      fun x => κ / 2 * (x ^ 2 * Real.exp (-(β * κ / 2) * x ^ 2)) := by
  sorry

-- BEGIN SPEC
theorem equipartition (κ : ℝ) (hκ : 0 < κ) (T : Temperature) (hT : 0 < T.val) :
    (harmonic κ).meanEnergy T = kB * T.toReal / 2 :=
-- END SPEC
  sorry

end H093

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With `a = βκ/2` the Boltzmann weight is the Gaussian `exp (-a x²)`, and the numerator is
    `κ/2 · ∫ x² exp (-a x²)`. The whole problem is the second moment `∫ x² e^{-a x²} = (1/(2a)) ∫ e^{-a x²}`;
    then `⟨E⟩ = κ/2 · 1/(βκ) = 1/(2β) = kB T / 2`.
H2. `moment2`: the integrand is even, so `integral_comp_abs` (with `f x = x ^ (2:ℝ) * exp (-a * x ^ (2:ℝ))`
    and `Real.rpow_two`, `sq_abs`) turns it into `2 * ∫ x in Ioi 0, …`; the Gamma formula with
    `p = q = 2` gives `a^(-3/2) · (1/2) · Γ(3/2)`, with `Γ(3/2) = √π / 2`. Compare with `integral_gaussian`.
    Main: `rw [meanEnergy_eq_ratio_of_integrals]`, then the milestones and `integral_const_mul`.
H3. Key rpow fact: `a ^ (-(3/2) : ℝ) = 1 / (a * √a)` via `Real.rpow_neg`, `3/2 = 1 + 1/2`, `Real.rpow_add`,
    `← Real.sqrt_eq_rpow`; then `Real.sqrt_div'` and `field_simp`. In the main proof, after
    `show (∫ x, (fun x => E x * exp (-β * E x)) x ∂volume) / (∫ x, (fun x => exp (-β * E x)) x ∂volume) = _`
    (with `E = (harmonic κ).energy`), `rw [integrand_eq, weight_eq, integral_const_mul, moment2 _ ha]`,
    cancel the positive Gaussian integral, `rw [Temperature.β_toReal]`, `field_simp`.
-/

/- H093 | Equipartition | 1-1.5 h | Gaussian integrals, Gamma function, rpow, CanonicalEnsemble on ℝ, physlib
GOAL
  `harmonic κ` is one classical harmonic degree of freedom: states `x : ℝ` with Lebesgue measure and
  energy `E(x) = κ x² / 2` (`κ > 0` the stiffness). Prove equipartition: at temperature `T > 0` its mean
  energy is `kB T / 2`, where `⟨E⟩ = (∫ E e^{-βE} dx) / (∫ e^{-βE} dx)` and `β = 1 / (kB T)`.

GUIDE
  Entries R1–R31: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · moment2   (milestone 1: ∫ x² e^{-ax²} = (1/(2a)) ∫ e^{-ax²}; used in equipartition)
  1. Fold the even integrand onto (0, ∞), with REAL powers on the right so step 2 matches:
       h1 : ∫ x, x ^ 2 * rexp (-a * x ^ 2) = 2 * ∫ x in Set.Ioi 0, x ^ (2:ℝ) * rexp (-a * x ^ (2:ℝ))
       proof: R1 with `(f := fun x : ℝ => …)`, then one `simp only` with   R2, R3
  2. rw [h1]; the Gamma formula with p = q = 2; the Gaussian on the right: R4, R5
  3. hG : Gamma ((2 + 1) / 2) = √π / 2         proof: R6 → R7 → R8, `ring`
  4. hpow : a ^ (-((2:ℝ) + 1) / 2) = 1 / (a * √a)
       proof: R6 (to `-(1 + 1 / 2)`) → R9 → R10, R11 → R12, `ring`
  5. hsa : 0 < √a (for `field_simp`):                                       R13
  6. rw [hG, hpow], split `√(π / a)`, clear the denominators:              R14, R15
-/
-- MILESTONE (optional: change or delete)
theorem moment2 (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-a * x ^ 2) = (1 / (2 * a)) * ∫ x : ℝ, Real.exp (-a * x ^ 2) := by
  sorry

/- SKELETON · weight_eq   (milestone 2: the Boltzmann weight is a Gaussian; used in equipartition)
  1. Equation of functions → equation at a point `x`:                       R16
  2. Unfold the energy field of `harmonic`:                                 R17
  3. The two exponents are ring-equal; close inside `rexp`:                 R18
-/
-- MILESTONE (optional: change or delete)
theorem weight_eq (κ β : ℝ) :
    (fun x : ℝ => Real.exp (-β * (harmonic κ).energy x)) =
      fun x => Real.exp (-(β * κ / 2) * x ^ 2) := by
  sorry

/- SKELETON · integrand_eq   (milestone 3: numerator integrand = κ/2 · second-moment integrand;
                             used in equipartition)
  Same three steps as weight_eq:                                            R16, R17, R18
-/
-- MILESTONE (optional: change or delete)
theorem integrand_eq (κ β : ℝ) :
    (fun x : ℝ => (harmonic κ).energy x * Real.exp (-β * (harmonic κ).energy x)) =
      fun x => κ / 2 * (x ^ 2 * Real.exp (-(β * κ / 2) * x ^ 2)) := by
  sorry

/- SKELETON · equipartition
  Prove the three milestones above first: integrand_eq, weight_eq (step 4) and moment2 (step 4).
  1. Mean energy → ratio of integrals:                                      R19
  2. hβ : 0 < (T.β : ℝ), then ha : 0 < (T.β : ℝ) * κ / 2:                   R20, R21
  3. Restate the goal with `∂volume`, as in W5:                             R22
       show (∫ x, E x * rexp (-(T.β : ℝ) * E x) ∂volume) /
         (∫ x, rexp (-(T.β : ℝ) * E x) ∂volume) = _
     with `E x` written out as `(harmonic κ).energy x`.
  4. Rewrite both integrands, pull out `κ / 2`, use the second moment:
       rw [integrand_eq, weight_eq] (R23), R24, rw [moment2 _ ha]
  5. hZ : 0 < ∫ x, rexp (-((T.β : ℝ) * κ / 2) * x ^ 2)      proof: R5, R21
  6. Cancel the Gaussian integral `Z`:                                      R25 → R26 → R27 → R28
  7. β in terms of kB and T; positivity facts; clear the denominators:      R29, R30, R31, R15
-/
-- BEGIN SPEC
theorem equipartition (κ : ℝ) (hκ : 0 < κ) (T : Temperature) (hT : 0 < T.val) :
    (harmonic κ).meanEnergy T = kB * T.toReal / 2 :=
-- END SPEC
  sorry

end H093

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With `a = βκ/2` the Boltzmann weight is the Gaussian `exp (-a x²)` and the numerator's integrand is
    `κ/2 · x² exp (-a x²)` (milestones 2, 3). Everything then hangs on the second moment
    `∫ x² e^{-a x²} = (1/(2a)) ∫ e^{-a x²}` (milestone 1): `⟨E⟩ = κ/2 · 1/(2a) = 1/(2β) = kB T / 2`.
H2. `moment2`: the integrand is even, so fold it onto `(0, ∞)` (R1–R3); the Gamma formula with `p = q = 2`
    (R4) gives `a^(-3/2) · (1/2) · Γ(3/2)` and the right side is `√(π/a)` (R5). Evaluate `Γ(3/2) = √π / 2`
    (R6–R8) and `a^(-3/2) = 1/(a √a)` (R9–R12) as `have`s, then `field_simp` (R13–R15).
    Milestones 2, 3: `funext x; simp only [harmonic]; ring_nf`.
    Main: R19, restate with `∂volume` (R22), rewrite with the milestones and `integral_const_mul`, cancel the
    positive Gaussian integral (R25–R28), then `Temperature.β_toReal` and `field_simp` with `0 < T.toReal`, `0 < kB`.
H3. `rw [← integral_comp_abs (f := fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-a * x ^ (2 : ℝ)))]`, then
    `simp only [Real.rpow_two, sq_abs]`. `hpow` starts with
    `rw [show -((2 : ℝ) + 1) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg ha.le, Real.rpow_add ha]`.
    Main: after `rw [meanEnergy_eq_ratio_of_integrals]` write
    `show (∫ x, E x * exp (-β * E x) ∂volume) / (∫ x, exp (-β * E x) ∂volume) = _`
    (with `E = (harmonic κ).energy`, `β = (T.β : ℝ)`), `rw [integrand_eq, weight_eq, integral_const_mul, moment2 _ ha]`,
    and `rw [← mul_assoc, mul_div_assoc, div_self hZ.ne', mul_one, Temperature.β_toReal]`.
-/

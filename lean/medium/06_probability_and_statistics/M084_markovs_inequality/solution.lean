/- M084 | Markov's inequality | 15 min | indicator, integral_mono, measurableSet_le, expectation, mathlib
GOAL
  Markov's inequality from scratch: for an integrable `X ≥ 0` and any real `c` (the content is `c > 0`),
  `c · P(X ≥ c) ≤ E[X]`. Compare `X` with the step function `c · 1{X ≥ c}` and integrate.

REFERENCE
  `μ[X]` is the expectation `∫ ω, X ω ∂μ`; `μ.real S : ℝ` is the probability of `S` as a real number.
  `S.indicator f ω` is `f ω` when `ω ∈ S` and `0` otherwise; `f ≤ g` on functions is `∀ ω, f ω ≤ g ω`.
  #check measurableSet_le           -- Measurable f → Measurable g → MeasurableSet {a | f a ≤ g a}
  #check measurable_const           -- Measurable fun _ => c
  #check integral_mono              -- Integrable f μ → Integrable g μ → f ≤ g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ
  #check Integrable.indicator       -- Integrable f μ → MeasurableSet s → Integrable (s.indicator f) μ
  #check integrable_const           -- (c) : Integrable (fun _ => c) μ     [IsFiniteMeasure μ]
  #check integral_indicator_const   -- (e) → MeasurableSet s → ∫ x, s.indicator (fun _ => e) x ∂μ = μ.real s • e
  #check Set.indicator_of_mem       -- a ∈ s → ∀ f, s.indicator f a = f a   (and `Set.indicator_of_notMem`)
  #check smul_eq_mul                -- a • b = a * b
BANNED: mul_meas_ge_le_integral_of_nonneg, mul_meas_ge_le_lintegral, mul_meas_ge_le_lintegral₀, meas_ge_le_lintegral_div, setIntegral_ge_of_const_le, setIntegral_ge_of_const_le_real, pow_mul_meas_ge_le_eLpNorm, mul_meas_ge_le_pow_eLpNorm, mul_meas_ge_le_pow_eLpNorm', meas_ge_le_mul_pow_eLpNorm_enorm, pow_mul_meas_ge_le_enorm, mul_meas_ge_le_pow_enorm, mul_meas_ge_le_pow_enorm', meas_ge_le_mul_pow_enorm
-/
import Mathlib

namespace M084

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X) (hX : Integrable X μ) (hnn : ∀ ω, 0 ≤ X ω)
    (c : ℝ) :
    c * μ.real {ω | c ≤ X ω} ≤ μ[X] :=
-- END SPEC
  by
    set S := {ω | c ≤ X ω}
    have hS : MeasurableSet S := measurableSet_le measurable_const hmeas
    have hle : S.indicator (fun _ => c) ≤ X := by
      intro ω
      by_cases h : ω ∈ S
      · rw [Set.indicator_of_mem h]
        exact h
      · rw [Set.indicator_of_notMem h]
        exact hnn ω
    have := integral_mono ((integrable_const c).indicator hS) hX hle
    rwa [integral_indicator_const c hS, smul_eq_mul, mul_comm] at this

end M084

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Let `S := {ω | c ≤ X ω}`. Pointwise, `S.indicator (fun _ => c) ω ≤ X ω`: on `S` it is `c ≤ X ω`,
    off `S` it is `0 ≤ X ω`.
H2. Integrate that pointwise inequality with `integral_mono`; the left integral is `μ.real S • c` by
    `integral_indicator_const`. You need `MeasurableSet S` for both steps.
H3. `have hS : MeasurableSet S := measurableSet_le measurable_const hmeas`;
    `have := integral_mono ((integrable_const c).indicator hS) hX hle`, then
    `rwa [integral_indicator_const c hS, smul_eq_mul, mul_comm] at this`.
-/

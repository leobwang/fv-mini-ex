/- M084 | Markov's inequality | 15 min | indicator, integral_mono, measurableSet_le, expectation, mathlib
GOAL
  Markov's inequality from scratch: for an integrable `X ≥ 0` and any real `c` (the content is `c > 0`),
  `c · P(X ≥ c) ≤ E[X]`. Compare `X` with the step function `c · 1{X ≥ c}` and integrate.
BANNED: mul_meas_ge_le_integral_of_nonneg, mul_meas_ge_le_lintegral, mul_meas_ge_le_lintegral₀, meas_ge_le_lintegral_div, setIntegral_ge_of_const_le, setIntegral_ge_of_const_le_real, pow_mul_meas_ge_le_eLpNorm, mul_meas_ge_le_pow_eLpNorm, mul_meas_ge_le_pow_eLpNorm', meas_ge_le_mul_pow_eLpNorm_enorm, pow_mul_meas_ge_le_enorm, mul_meas_ge_le_pow_enorm, mul_meas_ge_le_pow_enorm', meas_ge_le_mul_pow_enorm

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M084

/- SKELETON · markov
  1. Name the event, so every later step can say `S`:                         R1
       set S := {ω | c ≤ X ω}
  2. Its measurability, as a `have` with a term proof:                        R2 with R3
       hS : MeasurableSet S
  3. The pointwise comparison, as a `have` with its own `by` block:
       hle : S.indicator (fun _ => c) ≤ X
       open the function inequality:                                          R4
       split on whether `ω ∈ S`:                                              R5
         on S:  evaluate the indicator, then `h` itself is `c ≤ X ω`          R6, R7
         off S: evaluate the indicator, then `hnn ω`                          R8
  4. Integrate `hle`; the smaller side's integrability comes first:          R11
       its first argument: the constant is integrable, cut down to S          R9 → R10
       its second: `hX`; its third: `hle`
  5. Rewrite the new fact `this` until it is the goal, then close:            R12 → R13 → R14, R15
-/
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
H1. Let `S := {ω | c ≤ X ω}`. Pointwise, `S.indicator (fun _ => c) ω ≤ X ω`: on `S` it is `c ≤ X ω`
    (the membership itself), off `S` it is `0 ≤ X ω`. Integrate that inequality.
H2. `set S` (R1); `hS : MeasurableSet S` (R2, R3); `hle : S.indicator (fun _ => c) ≤ X` by
    `intro ω` and `by_cases h : ω ∈ S` (R4–R8). Then `integral_mono` (R11) on `hle`: the left integral
    is `μ.real S • c` by `integral_indicator_const` (R12); turn it into `c * μ.real S` (R13, R14),
    all by rewriting `this` (R15).
H3. `have hS : MeasurableSet S := measurableSet_le measurable_const hmeas`;
    `have := integral_mono ((integrable_const c).indicator hS) hX hle`, then
    `rwa [integral_indicator_const c hS, smul_eq_mul, mul_comm] at this`.
-/

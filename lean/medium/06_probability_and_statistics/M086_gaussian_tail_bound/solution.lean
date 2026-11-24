/- M086 | Gaussian tail bound | 15 min | mgf, gaussianReal, HasLaw, Chernoff bound, optimisation, mathlib
GOAL
  For `X ~ N(0, v)` with `v > 0` and `ε ≥ 0`: `P(X ≥ ε) ≤ exp(-ε² / (2v))`. Use the Chernoff bound
  `P(X ≥ ε) ≤ e^{-tε} M(t)` with the Gaussian mgf `M(t) = e^{v t² / 2}`, then choose the best `t`.
BANNED: HasSubgaussianMGF, HasSubgaussianMGF_iff_kernel, measure_ge_le, measure_ge_le_exp_add

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M086

/- SKELETON · gaussian_tail
  1. Facts about the numbers:
       hv' : (0 : ℝ) < v                (`v` cast into ℝ)                          R1
       t := ε / v, with ht : t = ε / v  (the minimiser of -t ε + v t² / 2)         R2
       ht0 : 0 ≤ t                      (from hε and hv')                          R3, R4
  2. The mgf at `t`, proved once (it is used in steps 3 and 4):
       hmgf : mgf X μ t = Real.exp (v * t ^ 2 / 2)                                 R5 → R6, then R7
  3. The integrability that Chernoff needs, from the positivity of the mgf:
       hint : Integrable (fun ω => Real.exp (t * X ω)) μ                           R8, rw [hmgf], R9
  4. Chain the bound and the exponent:                                             R10
       step 1  μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t                R11 with ht0, hint
       step 2  _ = Real.exp (-ε ^ 2 / (2 * v)):
                 one exponential                                                   rw [hmgf], R12
                 compare exponents                                                 R13
                 substitute t, clear denominators, finish                          rw [ht], R14, ring
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem gaussian_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (v : ℝ≥0) (hv : 0 < v) (hX : HasLaw X (gaussianReal 0 v) μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * v)) :=
-- END SPEC
  by
    have hv' : (0 : ℝ) < v := hv
    set t : ℝ := ε / v with ht
    have ht0 : 0 ≤ t := div_nonneg hε hv'.le
    have hmgf : mgf X μ t = Real.exp (v * t ^ 2 / 2) := by
      rw [mgf_gaussianReal hX.map_eq]; simp
    have hint : Integrable (fun ω => Real.exp (t * X ω)) μ :=
      mgf_pos_iff.mp (by rw [hmgf]; exact Real.exp_pos _)
    calc μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t := measure_ge_le_exp_mul_mgf ε ht0 hint
      _ = Real.exp (-ε ^ 2 / (2 * v)) := by
        rw [hmgf, ← Real.exp_add]; congr 1; rw [ht]; field_simp; ring

end M086

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Chernoff gives `P(X ≥ ε) ≤ exp (-t ε + v t² / 2)` for every `t ≥ 0`. Minimise the exponent over `t`:
    the best choice is `t = ε / v`, where it equals `-ε² / (2v)`.
H2. Name `t := ε / v` with `set` and prove `0 ≤ t`. Compute the mgf once (`hmgf`); its positivity gives the
    integrability Chernoff needs (`mgf_pos_iff`). Then `calc`: Chernoff, then an equality of exponentials,
    reduced to an equality of exponents (`← Real.exp_add`, `congr 1`) and closed by algebra after `rw [ht]`.
H3. `have hmgf : mgf X μ t = Real.exp (v * t ^ 2 / 2) := by rw [mgf_gaussianReal hX.map_eq]; simp`,
    `have hint : Integrable (fun ω => Real.exp (t * X ω)) μ := mgf_pos_iff.mp (by rw [hmgf]; exact Real.exp_pos _)`,
    first `calc` step `measure_ge_le_exp_mul_mgf ε ht0 hint`; the second ends `congr 1; rw [ht]; field_simp; ring`.
-/

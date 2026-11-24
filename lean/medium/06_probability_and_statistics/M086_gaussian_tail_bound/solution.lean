/- M086 | Gaussian tail bound | 15 min | mgf, gaussianReal, HasLaw, Chernoff bound, optimisation, mathlib
GOAL
  For `X ~ N(0, v)` with `v > 0` and `ε ≥ 0`: `P(X ≥ ε) ≤ exp(-ε² / (2v))`. Use the Chernoff bound
  `P(X ≥ ε) ≤ e^{-tε} M(t)` with the Gaussian mgf `M(t) = e^{v t² / 2}`, then choose the best `t`.

REFERENCE
  `HasLaw X ν P`: the law of `X` under `P` is `ν`. `gaussianReal m v` is `N(m, v)`
  with `v : ℝ≥0` (`ℝ≥0` = `NNReal`, the nonnegative reals; `(v : ℝ)` is its coercion).
  `mgf X μ t` is the moment generating function `μ[fun ω => Real.exp (t * X ω)]`.
  #check measure_ge_le_exp_mul_mgf  -- (ε) → 0 ≤ t → Integrable (fun ω => exp (t * X ω)) μ →
                                    --   μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t
  #check mgf_gaussianReal   -- μ.map X = gaussianReal m v → ∀ t, mgf X μ t = exp (m * t + v * t ^ 2 / 2)
  #check HasLaw.map_eq      -- HasLaw X ν P → P.map X = ν
  #check mgf_pos_iff        -- 0 < mgf X μ t ↔ Integrable (fun ω => exp (t * X ω)) μ
  #check Real.exp_add       -- exp (x + y) = exp x * exp y
  example (v : NNReal) (hv : 0 < v) : (0 : ℝ) < v := hv   -- move `0 < v` to the coercion `(v : ℝ)`
BANNED: HasSubgaussianMGF, HasSubgaussianMGF_iff_kernel, measure_ge_le, measure_ge_le_exp_add
NOTE: the goal mentions `(v : ℝ)`, the coercion of `v : ℝ≥0`; `field_simp` needs `(v : ℝ) ≠ 0` in context.
-/
import Mathlib

namespace M086

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
H1. Minimise `-t ε + v t² / 2` over `t ≥ 0`: the best choice is `t = ε / v`.
H2. With `t := ε / v`, first compute `mgf X μ t = exp (v * t ^ 2 / 2)`; it is positive, which gives
    the integrability that Chernoff needs. Then Chernoff plus `exp a * exp b = exp (a + b)`.
H3. `have hmgf : mgf X μ t = Real.exp (v * t ^ 2 / 2) := by rw [mgf_gaussianReal hX.map_eq]; simp`;
    `hint := mgf_pos_iff.mp (by rw [hmgf]; exact Real.exp_pos _)`; then
    `calc _ ≤ _ := measure_ge_le_exp_mul_mgf ε ht0 hint
          _ = _ := ?_`, and the exponents agree: `-t ε + v t² / 2 = -ε² / (2v)` at `t = ε / v`.
-/

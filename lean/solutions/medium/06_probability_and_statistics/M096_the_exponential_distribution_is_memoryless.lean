/- M096 | The exponential distribution is memoryless | 15-20 min | expMeasure, cdf, cond, ENNReal.ofReal, complements, mathlib
GOAL
  For `T ~ Exp(r)`: the tail is `P(T > x) = e^{-r x}` for `x ≥ 0`, and `T` is memoryless:
  `P(T > s + t | T > s) = P(T > t)` (having waited `s`, the remaining wait is again `Exp(r)`).

REFERENCE
  `expMeasure r : Measure ℝ` is `Exp(r)`; `Set.Ioi x = {y | x < y}` is the event `T > x`, `Set.Iic x` is `T ≤ x`.
  `μ[A | B]` (`open ProbabilityTheory`) is `P(A | B)`. Values are in `ℝ≥0∞`; `ENNReal.ofReal : ℝ → ℝ≥0∞`.
  `cdf μ x` is the real number `P(T ≤ x)`.
  #check cdf_expMeasure_eq     -- 0 < r → cdf (expMeasure r) x = if 0 ≤ x then 1 - exp (-(r * x)) else 0
  #check ofReal_cdf            -- [IsProbabilityMeasure μ] → ENNReal.ofReal (cdf μ x) = μ (Set.Iic x)
  #check isProbabilityMeasure_expMeasure  -- 0 < r → IsProbabilityMeasure (expMeasure r)   (`haveI := …`)
  #check prob_compl_eq_one_sub -- MeasurableSet s → μ sᶜ = 1 - μ s;  with `Set.compl_Iic : (Iic a)ᶜ = Ioi a`
  #check ENNReal.ofReal_sub    -- (p) → 0 ≤ q → ofReal (p - q) = ofReal p - ofReal q;  `ENNReal.ofReal_one`
  #check cond_apply            -- MeasurableSet s → ∀ μ t, μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)
  #check Set.Ioi_inter_Ioi     -- Ioi a ∩ Ioi b = Ioi (max a b)    (`max` may display as `a ⊔ b`)
  #check ENNReal.ofReal_mul    -- 0 ≤ p → ofReal (p * q) = ofReal p * ofReal q;  also `ENNReal.ofReal_inv_of_pos`
NOTE: `ring` cannot see through `ENNReal.ofReal`: gather everything into one `ofReal (…)`, then `congr 1` and `ring`.
-/
import Mathlib

namespace M096

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem exp_tail (r x : ℝ) (hr : 0 < r) (hx : 0 ≤ x) :
    expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) :=
-- END SPEC
  by
    haveI := isProbabilityMeasure_expMeasure hr
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hr,
      if_pos hx, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))]
    congr 1
    ring

-- BEGIN SPEC
theorem exp_memoryless (r s t : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (expMeasure r)[Set.Ioi (s + t) | Set.Ioi s] = expMeasure r (Set.Ioi t) :=
-- END SPEC
  by
    rw [cond_apply measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right (by linarith),
      exp_tail r (s + t) hr (by linarith), exp_tail r s hr hs, exp_tail r t hr ht,
      ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_neg, ← Real.exp_add]
    congr 2
    ring

end M096

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Tail: `T > x` is the complement of `T ≤ x`, whose probability is the cdf. Memoryless: use `exp_tail`
    three times; `{T > s} ∩ {T > s + t} = {T > s + t}`.
H2. Tail: `rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hx]`,
    then write `1` as `ofReal 1` and merge the subtraction into one `ofReal`. Memoryless: `cond_apply measurableSet_Ioi`,
    `Set.Ioi_inter_Ioi`, `max_eq_right`, `exp_tail`, then turn `(ofReal a)⁻¹ * ofReal b` into `ofReal (a⁻¹ * b)`.
H3. Tail ends with `← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sub_nonneg.mpr (Real.exp_le_one_iff.mpr _))`; memoryless
    ends with `← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity), ← Real.exp_neg, ← Real.exp_add`.
-/

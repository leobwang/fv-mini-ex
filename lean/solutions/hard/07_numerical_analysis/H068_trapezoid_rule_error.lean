/- H068 | Trapezoid rule error | 1-1.5 h | integration by parts, Peano kernel, HasDerivAt, integral bounds, mathlib
GOAL
  Trapezoid rule `T = (b - a)/2 · (f a + f b)`: if `|f''| ≤ M` on `[a, b]` then `|∫ₐᵇ f - T| ≤ M (b - a)³ / 12`
  (`f'`, `f''` come with `HasDerivAt` hypotheses). Route: the Peano kernel identity `∫ₐᵇ f - T = -∫ₐᵇ w f''`
  with `w t = (t - a)(b - t)/2` (integrate by parts twice), then bound the integral.

REFERENCE
  #check intervalIntegral.integral_mul_deriv_eq_deriv_mul  -- integration by parts:
    -- (∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) → (same for v, v') → IntervalIntegrable u' volume a b → (same for v') →
    --   ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x        (uIcc a b = [min a b, max a b])
  #check intervalIntegral.integral_eq_sub_of_hasDerivAt   -- (∀ x ∈ uIcc a b, HasDerivAt F (f x) x) → IntervalIntegrable f volume a b → ∫ x in a..b, f x = F b - F a
  example (a t : ℝ) : HasDerivAt (fun t => (t - a) ^ 2 / 2) (t - a) t :=
    (((hasDerivAt_id' t).sub_const a).pow 2).div_const 2 |>.congr_deriv (by simp)   -- `congr_deriv` fixes the derivative's form
  example (g g' : ℝ → ℝ) (h : ∀ t, HasDerivAt g (g' t) t) : Continuous g := continuous_iff_continuousAt.mpr fun t => (h t).continuousAt
  example (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) : IntervalIntegrable (fun t => |g t|) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun t => |g t|).intervalIntegrable a b
  #check intervalIntegral.abs_integral_le_integral_abs  -- a ≤ b → |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x|
  #check intervalIntegral.integral_mono_on  -- a ≤ b → IntervalIntegrable f .. → IntervalIntegrable g .. → (∀ x ∈ Icc a b, f x ≤ g x) → ∫ f ≤ ∫ g
  #check intervalIntegral.integral_const_mul  -- ∫ x in a..b, c * f x = c * ∫ x in a..b, f x   (also `integral_neg`)
BANNED: trapezoidal_error_le, trapezoidal_error_le_of_c2, trapezoidal_integral_one, trapezoidal_error, trapezoidal_integral
-/
import Mathlib

open Set intervalIntegral

namespace H068

-- MILESTONE (optional: change or delete)
/-- Peano kernel identity: the trapezoid error is minus the integral of `f''` against the kernel `w`. -/
theorem peano (f f' f'' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'') :
    (∫ t in a..b, f t) - (b - a) / 2 * (f a + f b) = -∫ t in a..b, (t - a) * (b - t) / 2 * f'' t := by
  have cf' : Continuous f' := continuous_iff_continuousAt.mpr fun t => (hf' t).continuousAt
  have cf : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  -- the kernel `w t = (t - a)(b - t)/2` has `w' t = (a + b - 2t)/2` and `w'' = -1`
  have hw : ∀ t, HasDerivAt (fun t => (t - a) * (b - t) / 2) ((a + b - 2 * t) / 2) t := by
    intro t
    have := (((hasDerivAt_id' t).sub_const a).mul
      ((hasDerivAt_const t b).sub (hasDerivAt_id' t))).div_const 2
    exact this.congr_deriv (by simp only [Pi.sub_apply]; ring)
  have hw' : ∀ t, HasDerivAt (fun t => (a + b - 2 * t) / 2) (-1) t := by
    intro t
    have := ((hasDerivAt_const t (a + b)).sub ((hasDerivAt_id' t).const_mul 2)).div_const 2
    exact this.congr_deriv (by ring)
  rw [integral_mul_deriv_eq_deriv_mul (fun t _ => hw t) (fun t _ => hf' t)
      ((by fun_prop : Continuous fun t : ℝ => (a + b - 2 * t) / 2).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _),
    integral_mul_deriv_eq_deriv_mul (fun t _ => hw' t) (fun t _ => hf t)
      intervalIntegrable_const (cf'.intervalIntegrable _ _)]
  simp only [neg_one_mul, integral_neg]
  ring

-- MILESTONE (optional: change or delete)
theorem kernel_integral (a b : ℝ) : ∫ t in a..b, (t - a) * (b - t) / 2 = (b - a) ^ 3 / 12 := by
  have hF : ∀ t ∈ uIcc a b, HasDerivAt (fun t => -(t - a) ^ 3 / 6 + (b - a) * (t - a) ^ 2 / 4)
      ((t - a) * (b - t) / 2) t := by
    intro t _
    have := ((((hasDerivAt_id' t).sub_const a).pow 3).neg.div_const 6).add
      ((((hasDerivAt_id' t).sub_const a).pow 2).const_mul (b - a) |>.div_const 4)
    exact this.congr_deriv (by push_cast; ring)
  rw [integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun t : ℝ => (t - a) * (b - t) / 2).intervalIntegrable _ _)]
  ring

-- MILESTONE (optional: change or delete)
theorem kernel_nonneg (a b t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ (t - a) * (b - t) / 2 := by
  obtain ⟨h1, h2⟩ := ht
  have : 0 ≤ (t - a) * (b - t) := mul_nonneg (by linarith) (by linarith)
  linarith

-- BEGIN SPEC
theorem trapezoid_error (f f' f'' : ℝ → ℝ) (a b M : ℝ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'')
    (hM : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |(∫ t in a..b, f t) - (b - a) / 2 * (f a + f b)| ≤ M * (b - a) ^ 3 / 12 :=
-- END SPEC
  by
    rw [peano f f' f'' a b hf hf' hcont, abs_neg]
    calc |∫ t in a..b, (t - a) * (b - t) / 2 * f'' t|
        ≤ ∫ t in a..b, |(t - a) * (b - t) / 2 * f'' t| := abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, M * ((t - a) * (b - t) / 2) := by
          apply integral_mono_on hab
          · exact (by fun_prop : Continuous fun t => |(t - a) * (b - t) / 2 * f'' t|).intervalIntegrable _ _
          · exact (by fun_prop : Continuous fun t : ℝ => M * ((t - a) * (b - t) / 2)).intervalIntegrable _ _
          · intro t ht
            rw [abs_mul, abs_of_nonneg (kernel_nonneg a b t ht), mul_comm]
            exact mul_le_mul_of_nonneg_right (hM t ht) (kernel_nonneg a b t ht)
      _ = M * (b - a) ^ 3 / 12 := by rw [integral_const_mul, kernel_integral]; ring

end H068

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Kernel `w t = (t - a)(b - t)/2` vanishes at both ends, `w' t = (a + b - 2t)/2`, `w'' = -1`. Integrating
    `∫ w f''` by parts twice moves both derivatives onto `w`; the boundary terms produce the trapezoid sum.
H2. `peano`: first prove `HasDerivAt` facts for `w` and `w'` (build them from `hasDerivAt_id'`, `hasDerivAt_const`,
    `.sub_const/.sub/.mul/.const_mul/.div_const`, finish with `congr_deriv (by ring)`), then rewrite with IBP twice.
    `kernel_integral`: FTC with antiderivative `-(t - a)³/6 + (b - a)(t - a)²/4`. Main: bound `|w f''| ≤ M w` on `[a, b]`.
H3. `peano`: `rw [integral_mul_deriv_eq_deriv_mul (fun t _ => hw t) (fun t _ => hf' t) _ _,
    integral_mul_deriv_eq_deriv_mul (fun t _ => hw' t) (fun t _ => hf t) _ _]; simp only [neg_one_mul, integral_neg]; ring`.
    Main: `rw [peano .., abs_neg]`, then `calc` through `∫ |w f''|` (`abs_integral_le_integral_abs hab`) and
    `∫ M * w` (`integral_mono_on hab _ _ ?_`; pointwise `rw [abs_mul, abs_of_nonneg (kernel_nonneg ..), mul_comm]`
    and `mul_le_mul_of_nonneg_right`), then `integral_const_mul, kernel_integral`.
-/

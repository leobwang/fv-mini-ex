/- H068 | Trapezoid rule error | 1-1.5 h | integration by parts, Peano kernel, HasDerivAt, integral bounds, mathlib
GOAL
  Trapezoid rule `T = (b - a)/2 · (f a + f b)`: if `|f''| ≤ M` on `[a, b]` then `|∫ₐᵇ f - T| ≤ M (b - a)³ / 12`
  (`f'`, `f''` come with `HasDerivAt` hypotheses). Route: the Peano kernel identity `∫ₐᵇ f - T = -∫ₐᵇ w f''`
  with `w t = (t - a)(b - t)/2` (integrate by parts twice), then bound the integral.
BANNED: trapezoidal_error_le, trapezoidal_error_le_of_c2, trapezoidal_integral_one, trapezoidal_error, trapezoidal_integral

GUIDE
  Entries R1–R33: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Set intervalIntegral

namespace H068

/- SKELETON · peano   (MILESTONE 1: used in step 1 of `trapezoid_error`)
  Kernel `w t = (t - a) * (b - t) / 2`, `w' t = (a + b - 2 * t) / 2`, `w'' = -1`.
  1. Continuity of f', for an integrability side condition of step 4:       R1, R2
       cf' : Continuous f'      (`Continuous f` is not needed)
  2. hw : ∀ t, HasDerivAt (fun t => (t - a) * (b - t) / 2) ((a + b - 2 * t) / 2) t
       `intro t`; build forward: R3 → R5, R4 and R3 → R6 (sub), then R7, R9
       fix the derivative: R10, then R11, then `ring`
  3. hw' : ∀ t, HasDerivAt (fun t => (a + b - 2 * t) / 2) (-1) t
       R4, R3 → R8, R6 (sub), R9; then R10 with `ring`
  4. Integrate by parts on the right side (u = w, v = f'):                   R12
       arguments: R13 (with hw, hf'), R15 → R14 (for w'), R14 (hcont)
     and again on the new integral `∫ w' x * f' x` (u = w', v = f):          R12
       arguments: R13 (with hw', hf), R16, R14 (cf')
       goal: `… - ((a + b - 2 * b) / 2 * f b - (a + b - 2 * a) / 2 * f a - ∫ x in a..b, -1 * f x))`
  5. One `simp only` with R17, R18; then `ring` (the boundary terms with `b - b`, `a - a` vanish)
-/
-- MILESTONE (optional: change or delete)
/-- Peano kernel identity: the trapezoid error is minus the integral of `f''` against the kernel `w`. -/
theorem peano (f f' f'' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'') :
    (∫ t in a..b, f t) - (b - a) / 2 * (f a + f b) = -∫ t in a..b, (t - a) * (b - t) / 2 * f'' t := by
  sorry

/- SKELETON · kernel_integral   (MILESTONE 2: used in the last `calc` step of `trapezoid_error`)
  1. hF : ∀ t ∈ uIcc a b, HasDerivAt (fun t => -(t - a) ^ 3 / 6 + (b - a) * (t - a) ^ 2 / 4)
            ((t - a) * (b - t) / 2) t
       `intro t _`; first summand R3 → R5 → R19 → R20 → R9, second R3 → R5 → R19 → R8 → R9, join with R6 (add)
       fix the derivative: R10, then R21, then `ring`
  2. Fundamental theorem of calculus:                                       R22 with hF and R15 → R14
  3. `ring` (the values at `a` contain `a - a`)
-/
-- MILESTONE (optional: change or delete)
theorem kernel_integral (a b : ℝ) : ∫ t in a..b, (t - a) * (b - t) / 2 = (b - a) ^ 3 / 12 := by
  sorry

/- SKELETON · kernel_nonneg   (MILESTONE 3: used twice in step 3 of `trapezoid_error`)
  1. Split the interval membership:                                         R23
  2. have h : 0 ≤ (t - a) * (b - t): R24, each factor by R25 (from the two halves of step 1)
  3. Divide by 2:                                                           R25
-/
-- MILESTONE (optional: change or delete)
theorem kernel_nonneg (a b t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ (t - a) * (b - t) / 2 := by
  sorry

/- SKELETON · trapezoid_error
  Prove the three MILESTONES first: step 1 uses `peano`, step 3 `kernel_nonneg`, step 4 `kernel_integral`.
  1. `rw` with `peano f f' f'' a b hf hf' hcont`, then R26
       goal: `|∫ t in a..b, (t - a) * (b - t) / 2 * f'' t| ≤ M * (b - a) ^ 3 / 12`
  2. `calc`, first step `≤ ∫ t in a..b, |(t - a) * (b - t) / 2 * f'' t|`:     R27
  3. second step `≤ ∫ t in a..b, M * ((t - a) * (b - t) / 2)`:                 R28 → three goals
       the two integrability goals:                                          R15 → R14 (each)
       the pointwise goal: `intro t ht`; R29, R30 (with `kernel_nonneg`), R31
         goal: `|f'' t| * ((t - a) * (b - t) / 2) ≤ M * ((t - a) * (b - t) / 2)`
         close with R32 (`hM t ht` and `kernel_nonneg`)
  4. last step `= M * (b - a) ^ 3 / 12`: R33, `kernel_integral`, then `ring`
-/
-- BEGIN SPEC
theorem trapezoid_error (f f' f'' : ℝ → ℝ) (a b M : ℝ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hcont : Continuous f'')
    (hM : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |(∫ t in a..b, f t) - (b - a) / 2 * (f a + f b)| ≤ M * (b - a) ^ 3 / 12 :=
-- END SPEC
  sorry

end H068

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Kernel `w t = (t - a)(b - t)/2` vanishes at both ends, `w' t = (a + b - 2t)/2`, `w'' = -1`. Integrating
    `∫ w f''` by parts twice (R12) moves both derivatives onto `w`; the boundary terms produce the trapezoid sum.
    The bound is then `|∫ w f''| ≤ ∫ w |f''| ≤ M ∫ w`, with `w ≥ 0` on `[a, b]` and `∫ₐᵇ w = (b - a)³/12`.
H2. `peano`: first prove `HasDerivAt` facts `hw` for `w` and `hw'` for `w'` (build them forward from
    `hasDerivAt_id'`, `hasDerivAt_const` with `.sub_const/.sub/.mul/.const_mul/.div_const`, R3–R9, and finish
    with `congr_deriv`, R10), then rewrite with integration by parts twice. `kernel_integral`: FTC (R22) with
    antiderivative `-(t - a)³/6 + (b - a)(t - a)²/4`. Main: `calc` through `∫ |w f''|` (R27) and `∫ M * w`
    (R28), pointwise `|w f''| = |f''| * w ≤ M * w` (R29–R32).
H3. `peano`: `rw [integral_mul_deriv_eq_deriv_mul (fun t _ => hw t) (fun t _ => hf' t) _ _,
    integral_mul_deriv_eq_deriv_mul (fun t _ => hw' t) (fun t _ => hf t) _ _]; simp only [neg_one_mul, integral_neg]; ring`.
    Main: `rw [peano .., abs_neg]`, then `calc` through `∫ |w f''|` (`abs_integral_le_integral_abs hab`) and
    `∫ M * w` (`integral_mono_on hab _ _ ?_`; pointwise `rw [abs_mul, abs_of_nonneg (kernel_nonneg ..), mul_comm]`
    and `mul_le_mul_of_nonneg_right`), then `integral_const_mul, kernel_integral`.
-/

/- E106 | Interval integrals | 2-3 min | intervalIntegral, integral_pow, integral_add, IntervalIntegrable, mathlib
GOAL
  Compute integrals `∫ x in a..b, f x` of polynomials: the power rule, the trapezoid rule is exact for
  linear functions, and linearity for an unknown integrable `f` whose integral is given.

REFERENCE
  `∫ x in a..b, f x` is the integral of `f` from `a` to `b` (Lebesgue measure `volume` by default).
  `IntervalIntegrable f volume a b`: `f` is integrable on `[a, b]`. Splitting a sum needs it for both parts.
  #check integral_pow   -- ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)
  #check integral_id    -- ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2
  #check intervalIntegral.integral_add        -- IntervalIntegrable f .. → IntervalIntegrable g .. → ∫ f + g = ∫ f + ∫ g
  #check intervalIntegral.integral_const_mul  -- ∫ x in a..b, r * f x = r * ∫ x in a..b, f x
  #check intervalIntegral.integral_const      -- ∫ x in a..b, c = (b - a) • c     (`smul_eq_mul` turns • into *)
  #check intervalIntegrable_const             -- IntervalIntegrable (fun _ => c) μ a b
  example (m a b : ℝ) : IntervalIntegrable (fun x => m * x) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b   -- continuous ⇒ integrable on [a, b]
NOTE: `simp` cannot integrate `m * x` on its own: pull `m` out with `integral_const_mul` first.
-/
import Mathlib

namespace E106

-- BEGIN SPEC
theorem integral_sq : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem trapezoid_exact_linear (m c a b : ℝ) :
    ∫ x in a..b, (m * x + c) = (b - a) * ((m * a + c) + (m * b + c)) / 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem integral_linear_comb (f : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (h : ∫ x in a..b, f x = 3) : ∫ x in a..b, (2 * f x + 1) = 6 + (b - a) :=
-- END SPEC
  sorry

end E106

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Power rule for the first; for the others, split the sum, pull out the constant factor, then compute.
H2. `rw [intervalIntegral.integral_add h1 h2]` needs integrability of both summands: for `m * x` use
    `Continuous.intervalIntegrable`, for `2 * f x` use `hf.const_mul 2`, for constants `intervalIntegrable_const`.
H3. `rw [integral_pow]; norm_num`; for the trapezoid:
    `rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]; ring`.
-/

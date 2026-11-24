/- M113 | Simpson's rule is exact for cubics | 10-15 min | intervalIntegral, integral_pow, integrability, ring, mathlib
GOAL
  Simpson's rule `(b - a)/6 · (f(a) + 4 f(m) + f(b))`, with midpoint `m = (a + b)/2`, integrates every
  cubic exactly: one degree more than its three nodes suggest (the `x³` error cancels by symmetry).

REFERENCE
  `∫ x in a..b, f x` is the integral of `f` from `a` to `b`; splitting a sum needs both parts integrable.
  #check intervalIntegral.integral_add        -- IntervalIntegrable f μ a b → IntervalIntegrable g μ a b → ∫ f + g = ∫ f + ∫ g
  #check intervalIntegral.integral_const_mul  -- ∫ x in a..b, r * f x = r * ∫ x in a..b, f x
  #check intervalIntegral.integral_const      -- ∫ x in a..b, c = (b - a) • c     (`smul_eq_mul` turns • into *)
  #check integral_pow   -- ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)
  #check integral_id    -- ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2
  example (c a b : ℝ) (n : ℕ) : IntervalIntegrable (fun x : ℝ => c * x ^ n) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b   -- continuous ⇒ integrable on [a, b]
  `c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3` parses as `((c₀ + c₁ * x) + c₂ * x ^ 2) + c₃ * x ^ 3`: split the last `+` first.
NOTE: `simp only [intervalIntegral.integral_const_mul]` leaves `∫ x in a..b, c₁ * x` alone (bare `x`); `rw` it instead.
-/
import Mathlib

namespace M113

-- BEGIN SPEC
-- the cubic c₀ + c₁ x + c₂ x² + c₃ x³
def cubic (c₀ c₁ c₂ c₃ x : ℝ) : ℝ := c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3
-- END SPEC

-- BEGIN SPEC
theorem simpson_exact (c₀ c₁ c₂ c₃ a b : ℝ) :
    ∫ x in a..b, cubic c₀ c₁ c₂ c₃ x =
      (b - a) / 6 * (cubic c₀ c₁ c₂ c₃ a + 4 * cubic c₀ c₁ c₂ c₃ ((a + b) / 2) + cubic c₀ c₁ c₂ c₃ b) :=
-- END SPEC
  by
    unfold cubic
    have i : ∀ (n : ℕ) (c : ℝ), IntervalIntegrable (fun x : ℝ => c * x ^ n) MeasureTheory.volume a b :=
      fun n c => Continuous.intervalIntegrable (by fun_prop) a b
    -- WHY: `integral_add` needs both summands integrable; the left ones are continuous too.
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) a b) (i 3 c₃),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) a b) (i 2 c₂),
      intervalIntegral.integral_add intervalIntegrable_const (Continuous.intervalIntegrable (by fun_prop) a b)]
    simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const,
      smul_eq_mul]
    -- WHY: simp cannot see `fun x => c₁ * x` as `fun x => c₁ * f x`, so this term needs an explicit `rw`.
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring

end M113

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compute the left side in closed form, then both sides are polynomials in `a, b, cᵢ`: `ring` compares them.
H2. `unfold cubic`, then peel off the three `+` with `intervalIntegral.integral_add` (outermost first), each time
    proving both summands integrable by continuity. Then pull constants out and apply the power rule.
H3. `rw [intervalIntegral.integral_add _ (i 3 c₃), intervalIntegral.integral_add _ (i 2 c₂), …]`, where
    `i n c : IntervalIntegrable (fun x => c * x ^ n) volume a b` and each `_` is the (also continuous) left summand;
    then `simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const, smul_eq_mul]`.
-/

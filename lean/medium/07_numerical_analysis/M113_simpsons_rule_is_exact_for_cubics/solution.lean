/- M113 | Simpson's rule is exact for cubics | 10-15 min | intervalIntegral, integral_pow, integrability, ring, mathlib
GOAL
  Simpson's rule `(b - a)/6 · (f(a) + 4 f(m) + f(b))`, with midpoint `m = (a + b)/2`, integrates every
  cubic exactly: one degree more than its three nodes suggest (the `x³` error cancels by symmetry).

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M113

-- BEGIN SPEC
-- the cubic c₀ + c₁ x + c₂ x² + c₃ x³
def cubic (c₀ c₁ c₂ c₃ x : ℝ) : ℝ := c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3
-- END SPEC

/- SKELETON · simpson_exact
  1. Unfold the spec function so the integrand is the polynomial:            R1
  2. Integrability of every monomial term, once, as a family:                R2
       i : ∀ (n : ℕ) (c : ℝ), IntervalIntegrable (fun x : ℝ => c * x ^ n) MeasureTheory.volume a b
       proof: R3 with (by R4) for the continuity
  3. Split the integral of the sum, outermost (last) `+` first, three times: R6, R6, R6
       right summand: `i 3 c₃`, then `i 2 c₂`, then R3 + R4 for `c₁ * x`
       left summand:  R3 + R4 (it is a continuous sum), last time R5 (constant `c₀`)
  4. Evaluate the four integrals with one `simp only`:                       R7, R8, R9, R10
     `∫ c₁ * x` survives it (bare `x`): rewrite it by hand                   R7 → R11
  5. Both sides are now polynomials in a, b, c₀…c₃:                          R12
-/
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
H1. Compute the left side in closed form: split the integral of the sum into four integrals and evaluate
    each (power rule). Then both sides are polynomials in `a, b, cᵢ`, and `ring` compares them.
H2. `unfold cubic`, then peel off the three `+` with `intervalIntegral.integral_add` (outermost first). Each
    split needs both summands integrable: get that from continuity (`Continuous.intervalIntegrable`,
    `fun_prop`) or `intervalIntegrable_const`. Then `simp only` pulls constants out and applies the power rule;
    the term `∫ c₁ * x` needs `rw [intervalIntegral.integral_const_mul, integral_id]`.
H3. `rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) a b) (i 3 c₃), …]`, where
    `i n c : IntervalIntegrable (fun x => c * x ^ n) MeasureTheory.volume a b`; then
    `simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const, smul_eq_mul]`.
-/

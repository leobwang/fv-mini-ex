/- E106 | Interval integrals | 2-3 min | intervalIntegral, integral_pow, integral_add, IntervalIntegrable, mathlib
GOAL
  Compute integrals `∫ x in a..b, f x` of polynomials: the power rule, the trapezoid rule is exact for
  linear functions, and linearity for an unknown integrable `f` whose integral is given.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E106

/- SKELETON · integral_sq
  1. Power rule: the integral → `(1 ^ (2 + 1) - 0 ^ (2 + 1)) / (↑2 + 1)`:                R1
  2. Close the numeral goal:                                                              R2
-/
-- BEGIN SPEC
theorem integral_sq : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 :=
-- END SPEC
  sorry

/- SKELETON · trapezoid_exact_linear
  1. Split `∫ (m * x + c)` into `∫ m * x` + `∫ c`:                                         R3
       its argument for `fun x => m * x`: continuous, hence integrable                    R4 → R5
       its argument for `fun x => c`: a constant                                          R6
     (or `rw` with no arguments, then prove `case hf` and `case hg` after it: W2)
  2. Pull `m` out of the first integral:                                                  R7
  3. Closed forms: `∫ x` and `∫ c`, then `•` → `*`:                                      R8, R9, R10
  4. Close the polynomial identity:                                                       R11
-/
-- BEGIN SPEC
theorem trapezoid_exact_linear (m c a b : ℝ) :
    ∫ x in a..b, (m * x + c) = (b - a) * ((m * a + c) + (m * b + c)) / 2 :=
-- END SPEC
  sorry

/- SKELETON · integral_linear_comb
  1. Split `∫ (2 * f x + 1)`:                                                             R3
       its argument for `fun x => 2 * f x`: from `hf`                                     R12
       its argument for `fun x => 1`: a constant                                          R6
  2. Pull `2` out, so that `∫ (x : ℝ) in a..b, f x` stands alone:                        R7
  3. Substitute the known integral:                                                       rw [h]
  4. `∫ 1` → `(b - a) • 1` → `(b - a) * 1`:                                              R9, R10
  5. Close the identity:                                                                  R11
-/
-- BEGIN SPEC
theorem integral_linear_comb (f : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (h : ∫ x in a..b, f x = 3) : ∫ x in a..b, (2 * f x + 1) = 6 + (b - a) :=
-- END SPEC
  sorry

end E106

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first is the power rule `integral_pow` plus arithmetic. The others: split the integral of the sum,
    pull the constant factor out, then use the closed forms for `∫ x` and `∫ c` (or the hypothesis `h`).
H2. `rw [intervalIntegral.integral_add h1 h2]` needs integrability of both summands: for `fun x => m * x`
    use `Continuous.intervalIntegrable (by fun_prop) _ _`, for `fun x => 2 * f x` use `hf.const_mul 2`, for
    a constant `intervalIntegrable_const`. Then `intervalIntegral.integral_const_mul`, `integral_id` or
    `h`, `intervalIntegral.integral_const`, `smul_eq_mul`, and `ring`.
H3. `rw [integral_pow]; norm_num`. For the trapezoid:
    `rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]; ring`.
-/

/- E067 | linear_combination | 2-3 min | linear_combination, equational reasoning, mathlib
GOAL
  Prove an equation by naming the combination of hypotheses that yields it; `linear_combination` checks the
  rest with `ring`. It works in any commutative ring, including ℂ, where `linarith` (which needs `≤`) cannot.

REFERENCE
  example (a b : ℝ) (h : a = 2 * b) (hb : b = 1) : a = 2 := by linear_combination h + 2 * hb
  `linear_combination e₁ * h₁ + e₂ * h₂` proves `lhs = rhs` when
     (lhs - rhs) - (e₁ * (lhs₁ - rhs₁) + e₂ * (lhs₂ - rhs₂)) = 0   holds by `ring`.
  Above: (a - 2) - ((a - 2 * b) + 2 * (b - 1)) = 0.  Coefficients may be any terms: `(a + 1) * h`, `h / 2`, `-x * h`.
BANNED: linarith, nlinarith, grind, field_simp, rw, rwa, subst, simp, simp_all, norm_num, ring_nf, polyrith, exact?, apply?, try?
NOTE: `ring` alone is allowed but cannot use hypotheses; `linear_combination` is how they enter.
-/
import Mathlib

namespace E067

-- BEGIN SPEC
theorem lc_linear (x y : ℝ) (h1 : x + y = 5) (h2 : x - y = 1) : x = 3 :=
-- END SPEC
  by linear_combination (h1 + h2) / 2

-- BEGIN SPEC
theorem lc_square (a b : ℝ) (h : a + b = 3) (h2 : a * b = 2) : a ^ 2 + b ^ 2 = 5 :=
-- END SPEC
  by linear_combination (a + b + 3) * h - 2 * h2

-- BEGIN SPEC
theorem lc_complex (x y : ℂ) (h1 : x * y = 1) (h2 : x = 2) : y = 1 / 2 :=
-- END SPEC
  by linear_combination h1 / 2 - y / 2 * h2

end E067

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write the goal as `lhs - rhs` and each hypothesis as `lhsᵢ - rhsᵢ`; look for coefficients that make
    the combination equal to the goal's difference.
H2. `lc_linear`: add the equations and halve. `lc_square`: `a² + b² - 5` is `(a + b)² - 9` minus `2(ab - 2)`,
    and `(a + b)² - 9 = (a + b + 3)(a + b - 3)`. `lc_complex`: halve `h1`, then cancel the leftover `x` with `h2`.
H3. `lc_linear`: `linear_combination (h1 + h2) / 2`. `lc_square`: `linear_combination (a + b + ?) * h - ? * h2`.
-/

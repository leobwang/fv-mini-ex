/- E067 | linear_combination | 2-3 min | linear_combination, equational reasoning, mathlib
GOAL
  Prove an equation by naming the combination of hypotheses that yields it; `linear_combination` checks the
  rest with `ring`. It works in any commutative ring, including ℂ, where `linarith` (which needs `≤`) cannot.

BANNED: linarith, nlinarith, grind, field_simp, rw, rwa, subst, simp, simp_all, norm_num, ring_nf, polyrith, exact?, apply?, try?

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E067

/- SKELETON · lc_linear
  1. Write the goal as the difference `x - 3`, the hypotheses as `x + y - 5` and `x - y - 1`.
  2. Combine so the `y` cancels: add the two equations; this gives `2 * x - 6`:   R3
  3. Scale down to the goal's difference `x - 3`:                                R4
  4. One `linear_combination` call with that combination; to check your
     coefficients first, look at the identity it leaves with `(norm := skip)`:  R1 (R2)
-/
-- BEGIN SPEC
theorem lc_linear (x y : ℝ) (h1 : x + y = 5) (h2 : x - y = 1) : x = 3 :=
-- END SPEC
  by linear_combination (h1 + h2) / 2

/- SKELETON · lc_square
  1. Split the goal's difference `a ^ 2 + b ^ 2 - 5` into a square part and a
     product part: `((a + b) ^ 2 - 9) - 2 * (a * b - 2)`.
  2. Square part: factor `(a + b) ^ 2 - 9` by `a + b - 3`; the other factor is
     the term coefficient of `h`:                                                R5
  3. Product part: subtract the numeral multiple of `h2`:                        R6
  4. One `linear_combination` call with the sum of both:                         R1 (R2 to check)
-/
-- BEGIN SPEC
theorem lc_square (a b : ℝ) (h : a + b = 3) (h2 : a * b = 2) : a ^ 2 + b ^ 2 = 5 :=
-- END SPEC
  by linear_combination (a + b + 3) * h - 2 * h2

/- SKELETON · lc_complex
  1. The goal's difference is `y - 1 / 2`. Halve `h1`: it stands for
     `x * y / 2 = 1 / 2`:                                                        R4
  2. The leftover `y - x * y / 2` is a term multiple of `x - 2`; cancel it by
     subtracting that multiple of `h2` (its coefficient mentions `y`):           R6, R5
  3. One `linear_combination` call with the combination:                         R1 (R2 to check)
-/
-- BEGIN SPEC
theorem lc_complex (x y : ℂ) (h1 : x * y = 1) (h2 : x = 2) : y = 1 / 2 :=
-- END SPEC
  by linear_combination h1 / 2 - y / 2 * h2

end E067

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write the goal as `lhs - rhs` and each hypothesis as `lhsᵢ - rhsᵢ`; look for coefficients that make
    the combination equal to the goal's difference. `linear_combination (norm := skip) e` shows the
    identity your coefficients must satisfy (R2).
H2. `lc_linear`: add the equations and halve (R3, R4). `lc_square`: `a² + b² - 5` is `(a + b)² - 9` minus
    `2(ab - 2)`, and `(a + b)² - 9 = (a + b + 3)(a + b - 3)` (R5, R6). `lc_complex`: halve `h1`, then cancel
    the leftover `y - x y / 2 = -(y / 2)(x - 2)` with a multiple of `h2` (R4, R6).
H3. `lc_linear`: `linear_combination (h1 + h2) / 2`. `lc_square`: `linear_combination (a + b + ?) * h - ? * h2`.
    `lc_complex`: `linear_combination h1 / 2 - ? * h2`, where `?` is a term in `y`.
-/

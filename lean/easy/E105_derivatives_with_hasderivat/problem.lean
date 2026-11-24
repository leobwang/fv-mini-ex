/- E105 | Derivatives with HasDerivAt | 2-3 min | HasDerivAt, deriv, product rule, congr_deriv, mathlib
GOAL
  Build derivative facts from the library's rules (power, sum, constant multiple, product), then read
  off `deriv` at a point for a function built from an unknown `f` whose `HasDerivAt` fact is given.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E105

/- SKELETON · deriv_cubic
  (A proof term after `:=`, or `by exact …`; inspect pieces with `have h := …` first.)
  1. The derivative of each summand at `a`:  `x ^ 3`  and  `fun x => x`                R1, R2
  2. Scale the second by 2, then add the two facts:                                    R3, R4
       the function is now right (as `(fun x => x ^ 3) + fun y => 2 * y`), the
       derivative is the raw `↑3 * a ^ (3 - 1) + 2 * 1`
  3. Restate the derivative as `3 * a ^ 2 + 2`; the side equation is numerals:         R5 → R6
-/
-- BEGIN SPEC
theorem deriv_cubic (a : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3 + 2 * x) (3 * a ^ 2 + 2) a :=
-- END SPEC
  sorry

/- SKELETON · hasDerivAt_exp_mul_sin
  1. The derivatives of `Real.exp` and `Real.sin` at `x`:                             R7, R8
  2. Combine them with the product rule; its derivative is already the asked one,
     and its function `Real.exp * Real.sin` is the goal's lambda by definition:        R9
-/
-- BEGIN SPEC
theorem hasDerivAt_exp_mul_sin (x : ℝ) :
    HasDerivAt (fun t => Real.exp t * Real.sin t)
      (Real.exp x * Real.sin x + Real.exp x * Real.cos x) x :=
-- END SPEC
  sorry

/- SKELETON · deriv_two_mul
  1. From `hf`, the fact for `fun x => 2 * f x` (a lambda, so `rw` can match it):     R3
  2. Rewrite `deriv (fun x => 2 * f x) 0` to its value with that fact:                 R10
  3. Close the numeral goal that is left:                                              R6
-/
-- BEGIN SPEC
theorem deriv_two_mul (f : ℝ → ℝ) (hf : HasDerivAt f 3 0) : deriv (fun x => 2 * f x) 0 = 6 :=
-- END SPEC
  sorry

end E105

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every derivative here is assembled from library facts, never computed by unfolding `deriv`: the
    power rule, `fun x => x`, `exp` and `sin` (R1, R2, R7, R8), glued by `.const_mul`, `.add`, `.mul`
    (R3, R4, R9). A `deriv` goal is answered by a `HasDerivAt` fact (R10).
H2. `deriv_cubic`: `(hasDerivAt_pow 3 a).add (...)` has the right function but the raw derivative
    `↑3 * a ^ (3 - 1) + 2 * 1`; fix it with `.congr_deriv (by norm_num)`. The product is a single `.mul`.
    `deriv_two_mul`: build the fact for `fun x => 2 * f x` with `hf.const_mul 2`, then rewrite.
H3. `deriv_cubic`: the second summand is `(hasDerivAt_id' a).const_mul 2`.
    `deriv_two_mul`: `rw [(hf.const_mul 2).deriv]` leaves only `2 * 3 = 6`.
-/

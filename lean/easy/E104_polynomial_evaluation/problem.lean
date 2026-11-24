/- E104 | Polynomial evaluation | 2-3 min | Polynomial, eval, C, X, IsRoot, simp, mathlib
GOAL
  Evaluate real polynomials at points: a concrete quadratic, a product of unknown polynomials whose
  values are given, and a product with a factor that has a root. `p.eval x` is "the value of p at x".

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E104

/- SKELETON · eval_quadratic
  1. Push `eval` through the operations, outermost first:                  R1, R2, R4, R3
  2. Replace the variable by the point and the numeral polynomials by
     numerals (`eval 3 2`, `eval 3 1`):                                    R5, R7
  3. Close the arithmetic. `norm_num` alone also does steps 1–2:           R8
-/
-- BEGIN SPEC
open Polynomial

theorem eval_quadratic : (X ^ 2 - 2 * X + 1 : ℝ[X]).eval 3 = 4 :=
-- END SPEC
  sorry

/- SKELETON · eval_product
  1. Push `eval` down to `eval x p` and `eval x q`, outermost `+` first:   R1, R3, R6
  2. Substitute the known values:                                          rw [hp, hq]
  3. Close the arithmetic:                                                 R8
-/
-- BEGIN SPEC
theorem eval_product (p q : ℝ[X]) (x : ℝ) (hp : p.eval x = 2) (hq : q.eval x = 5) :
    (p * q + C 1).eval x = 11 :=
-- END SPEC
  sorry

/- SKELETON · eval_root_factor
  1. Turn the root hypothesis into h0 : eval r p = 0:                      R9
  2. Push `eval` through the product:                                      R3
  3. Substitute h0, then `0 * a = 0`:                                      rw [h0], R10
     (`simp` given the equation from step 1 does steps 2–3 in one call)
-/
-- BEGIN SPEC
theorem eval_root_factor (p : ℝ[X]) (r : ℝ) (h : p.IsRoot r) : (p * (X - C 7)).eval r = 0 :=
-- END SPEC
  sorry

end E104

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `eval` turns `+`, `-`, `*`, `^`, `X`, `C a` and numerals inside a polynomial into the same operations on
    numbers (R1–R7). A root `h : p.IsRoot r` is the equation `eval r p = 0` in disguise (R9).
H2. `eval_quadratic`: push `eval` all the way in and compute; `norm_num` does both. `eval_product`: push
    `eval` down to `eval x p` and `eval x q` with `eval_add`, `eval_mul`, `eval_C`, substitute `hp`, `hq`,
    compute. `eval_root_factor`: get `eval r p = 0` from `h`, push `eval` through `*`, and the factor `0`
    kills the product.
H3. `norm_num`; `rw [eval_add, eval_mul, eval_C, hp, hq]` then `norm_num`; `simp [h.eq_zero]`.
-/

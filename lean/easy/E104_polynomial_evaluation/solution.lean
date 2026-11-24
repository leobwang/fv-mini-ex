/- E104 | Polynomial evaluation | 2-3 min | Polynomial, eval, C, X, IsRoot, simp, mathlib
GOAL
  Evaluate real polynomials at points: a concrete quadratic, a product of unknown polynomials whose
  values are given, and a product with a factor that has a root. `p.eval x` is "the value of p at x".

REFERENCE
  `open Polynomial` gives `ℝ[X]` (polynomials with real coefficients), `X` (the variable) and
  `C a` (the constant polynomial `a`). `p.eval x : ℝ` plugs `x` in for `X`.
  #check eval_add   -- (p + q).eval x = p.eval x + q.eval x   (also eval_sub, eval_mul)
  #check eval_C     -- (C a).eval x = a
  #check eval_X     -- X.eval x = x
  #check eval_pow   -- (p ^ n).eval x = p.eval x ^ n
  #check IsRoot.eq_zero   -- p.IsRoot r → p.eval r = 0      (`p.IsRoot r` means `p.eval r = 0`)
  example : (X + C 2 : ℝ[X]).eval 1 = 3 := by norm_num   -- simp/norm_num know every eval_* lemma
-/
import Mathlib

namespace E104

-- BEGIN SPEC
open Polynomial

theorem eval_quadratic : (X ^ 2 - 2 * X + 1 : ℝ[X]).eval 3 = 4 :=
-- END SPEC
  by norm_num

-- BEGIN SPEC
theorem eval_product (p q : ℝ[X]) (x : ℝ) (hp : p.eval x = 2) (hq : q.eval x = 5) :
    (p * q + C 1).eval x = 11 :=
-- END SPEC
  by
    rw [eval_add, eval_mul, eval_C, hp, hq]
    norm_num

-- BEGIN SPEC
theorem eval_root_factor (p : ℝ[X]) (r : ℝ) (h : p.IsRoot r) : (p * (X - C 7)).eval r = 0 :=
-- END SPEC
  by simp [h.eq_zero]

end E104

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `eval` turns `+`, `*`, `^`, `C`, `X` inside the polynomial into the same operations on numbers.
H2. Rewrite `(p * q + C 1).eval x` step by step with `eval_add`, `eval_mul`, `eval_C`, then use `hp`, `hq`.
    For the root, turn `h` into `p.eval r = 0` first.
H3. `eval_product`: `rw [eval_add, eval_mul, eval_C, hp, hq]` then close the arithmetic. The concrete
    quadratic is a `norm_num` job; for the root, feed `h.eq_zero` to `simp`.
-/

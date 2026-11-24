/- E105 | Derivatives with HasDerivAt | 2-3 min | HasDerivAt, deriv, product rule, congr_deriv, mathlib
GOAL
  Build derivative facts from the library's rules (power, sum, constant multiple, product), then read
  off `deriv` at a point for a function built from an unknown `f` whose `HasDerivAt` fact is given.

REFERENCE
  `HasDerivAt f f' a`: `f : ℝ → ℝ` is differentiable at `a` with derivative the number `f'`.
  `deriv f a : ℝ` is that number (and junk `0` if `f` is not differentiable at `a`).
  #check hasDerivAt_pow   -- (n : ℕ) (x : 𝕜) : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x
  #check hasDerivAt_id'   -- (x : 𝕜) : HasDerivAt (fun x => x) 1 x
  #check Real.hasDerivAt_exp   -- (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x   (also hasDerivAt_sin)
  `hf.add hg` (f' + g'), `hf.const_mul c` (c * f'), `hf.mul hg` (f' * g x + f x * g'): combine facts.
  #check HasDerivAt.congr_deriv   -- HasDerivAt f f' x → f' = g' → HasDerivAt f g' x
  #check HasDerivAt.deriv         -- HasDerivAt f f' x → deriv f x = f'
NOTE: the rules produce derivatives like `↑3 * a ^ (3 - 1) + 2 * 1`; fix the shape with `congr_deriv`.
-/
import Mathlib

namespace E105

-- BEGIN SPEC
theorem deriv_cubic (a : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3 + 2 * x) (3 * a ^ 2 + 2) a :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem hasDerivAt_exp_mul_sin (x : ℝ) :
    HasDerivAt (fun t => Real.exp t * Real.sin t)
      (Real.exp x * Real.sin x + Real.exp x * Real.cos x) x :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem deriv_two_mul (f : ℝ → ℝ) (hf : HasDerivAt f 3 0) : deriv (fun x => 2 * f x) 0 = 6 :=
-- END SPEC
  sorry

end E105

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Assemble the derivative of `x ^ 3 + 2 * x` from `hasDerivAt_pow 3 a` and `hasDerivAt_id' a`.
H2. Combining with `.add` and `.const_mul` gives the right function but a derivative of the wrong
    shape: fix it with `.congr_deriv`. The product is one `.mul`. For `deriv`, first build a
    `HasDerivAt` fact for `fun x => 2 * f x` from `hf`.
H3. `deriv_two_mul`: `rw [(hf.const_mul 2).deriv]` leaves only arithmetic.
-/

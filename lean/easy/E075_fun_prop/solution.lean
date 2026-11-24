/- E075 | fun_prop | 2 min | fun_prop, Continuous, Differentiable, ContinuousAt, disch, mathlib
GOAL
  Prove continuity and differentiability of functions built from known pieces with `fun_prop`, and pass
  it a discharger when a side condition appears (such as `x ≠ 0` for `Real.log`).

REFERENCE
  example : Continuous (fun x : ℝ => Real.sin x + x ^ 3) := by fun_prop
  example : Differentiable ℝ (fun x : ℝ => Real.exp (2 * x)) := by fun_prop   -- `Differentiable 𝕜 f`: field first
  example : ContinuousAt (fun x : ℝ => 1 / x) 3 := by fun_prop (disch := norm_num)   -- side goal `3 ≠ 0`
  `fun_prop` splits `fun x => …` into sums, products and compositions and uses the lemma registered for
  each piece (exp, sin, cos, log, powers) or a hypothesis in context such as `hf : Continuous f`.
  `ContinuousAt f a` means continuous at the single point `a`; `Real.log` is continuous at every `a ≠ 0`.
  Without `(disch := …)`, `fun_prop` fails when a piece needs a side condition it cannot see.
BANNED: continuity
-/
import Mathlib

namespace E075

-- BEGIN SPEC
theorem cont_poly : Continuous (fun x : ℝ => x ^ 2 + 3 * x + 1) :=
-- END SPEC
  by fun_prop

-- BEGIN SPEC
theorem cont_exp_sin : Continuous (fun x : ℝ => Real.exp x * Real.sin x) :=
-- END SPEC
  by fun_prop

-- BEGIN SPEC
theorem diff_cos_exp : Differentiable ℝ (fun x : ℝ => Real.cos (x ^ 2) * Real.exp (2 * x)) :=
-- END SPEC
  by fun_prop

-- BEGIN SPEC
theorem cont_comb (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x + f (g x)) :=
-- END SPEC
  by fun_prop

-- BEGIN SPEC
theorem contAt_log_sin : ContinuousAt (fun y : ℝ => Real.log y * Real.sin y) 2 :=
-- END SPEC
  by fun_prop (disch := norm_num)  -- WHY: `Real.log` needs the side goal `(2 : ℝ) ≠ 0`

end E075

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every function here is built from continuous/differentiable pieces by `+`, `*` and composition.
H2. `fun_prop` handles the first four directly (it uses `hf`, `hg` from the context). The last one has a
    side condition from `Real.log` at the point 2.
H3. `fun_prop` four times; `fun_prop (disch := norm_num)` for `contAt_log_sin`.
-/

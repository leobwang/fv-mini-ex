/- M182 | The curl of a gradient vanishes | 10-15 min | Space.curl, Space.grad, ext, Schwarz via IsSymmSndFDerivAt, fderiv_clm_apply, physlib
GOAL
  For a twice continuously differentiable scalar field `f` on 3D space, `∇ × (∇ f) = 0`, using physlib's
  definitions of `curl` and `grad`. Prove Schwarz's theorem for `∂[i]` yourself, from Mathlib's
  symmetry of the second Fréchet derivative.

REFERENCE
  `Space` is `Space 3` (3D space); `∂[i] f x` (`Space.deriv i f x`) is the partial derivative ∂f/∂xᵢ at `x`.
  `∇ f` is `Space.grad f` (component `i` is `∂[i] f x`); `∇ ⨯ F` is `Space.curl F`: component `i` is
  `∂[i+1] F_{i+2} - ∂[i+2] F_{i+1}` (indices wrap in `Fin 3`), e.g.
  example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) :
    (∇ ⨯ F) x 0 = ∂[1] (fun y => F y 2) x - ∂[2] (fun y => F y 1) x := rfl
  #check Space.deriv_eq_fderiv_fun  -- ∂[μ] f = fun x => fderiv ℝ f x (basis μ)   (pointwise: `Space.deriv_eq`)
  #check fderiv_clm_apply  -- c, u differentiable at x → fderiv (fun y => c y (u y)) x = c x ∘L fderiv u x + (fderiv c x).flip (u x)
  example (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (x : Space) : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp)  -- `.eq v w : fderiv ℝ (fderiv ℝ f) x v w = … x w v`
  `unfold Space.curl Space.grad; ext i; simp only [PiLp.zero_apply]` exposes component `i` of both sides.
  `ContDiff ℝ 2 f`: `f` is C²; `fun_prop` proves differentiability side goals, e.g. of `fun y => fderiv ℝ f y`.
BANNED: curl_of_grad_eq_zero, deriv_commute, exact?, apply?, rw?, hint, observe, try?
-/
import Physlib.SpaceAndTime.Space.Derivatives.Curl

open Space

namespace M182

-- BEGIN SPEC
theorem curl_grad_eq_zero (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (x : Space) :
    (∇ ⨯ (∇ f)) x = 0 :=
-- END SPEC
  sorry

end M182

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Component `i` of the left side is a difference of two mixed second partial derivatives of `f`. So first
    prove, as a helper lemma, that mixed partials commute: `∂[i] (∂[j] f) x = ∂[j] (∂[i] f) x`.
H2. Helper: rewrite the inner `∂[j] f` as the function `fun y => fderiv ℝ f y (basis j)`, the outer one with
    `Space.deriv_eq`, and differentiate the application with `fderiv_clm_apply` (the argument `basis j` is
    constant, so `simp` removes that term). Both sides become `fderiv ℝ (fderiv ℝ f) x (basis _) (basis _)`.
H3. Helper ends with `exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _`. Main:
    `unfold Space.curl Space.grad; ext i; simp only [PiLp.zero_apply]; rw [helper f hf]; simp`.
-/

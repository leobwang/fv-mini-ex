/- M182 | The curl of a gradient vanishes | 10-15 min | Space.curl, Space.grad, ext, Schwarz via IsSymmSndFDerivAt, fderiv_clm_apply, physlib
GOAL
  For a twice continuously differentiable scalar field `f` on 3D space, `∇ × (∇ f) = 0`, using physlib's
  definitions of `curl` and `grad`. Prove Schwarz's theorem for `∂[i]` yourself, from Mathlib's
  symmetry of the second Fréchet derivative.
BANNED: curl_of_grad_eq_zero, deriv_commute, exact?, apply?, rw?, hint, observe, try?

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.SpaceAndTime.Space.Derivatives.Curl

open Space

namespace M182

/- SKELETON · curl_grad_eq_zero
  MILESTONE first: above this theorem (outside the spec), state and prove a helper
       theorem mixed_partials (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin 3) (x : Space) :
           ∂[i] (∂[j] f) x = ∂[j] (∂[i] f) x
     1. Inner `∂`s (functions) → `fderiv`, one per side, naming `j f` / `i f`:     R1, R1
     2. Outer `∂`s (values at `x`) → `fderiv … (basis _)`:                          R2, R2
     3. Product rule on each side, side goals by `(by fun_prop)`:                  R3 + R4, R3 + R4
     4. `simp`: constant's derivative, `∘L 0`, `0 + _`, `flip`:                     R5 → R6 → R7
     5. Goal is now `D²f(x) e_i e_j = D²f(x) e_j e_i`: Schwarz                      R8 → R9 → R10
  Main proof (uses the milestone in step 4):
     1. Unfold both operators:                                                      R11, R12
     2. Vector equation → component `i`:                                            R13
     3. Clean `have`, `toLp`/`ofLp` and the zero component:                         R14, R15
     4. The goal is `∂[i+1] ∂[i+2] f - ∂[i+2] ∂[i+1] f = 0`: rewrite the first term
        with the milestone `mixed_partials f hf`:                                   R16
     5. Close `a - a = 0`:                                                          R17
-/
-- BEGIN SPEC
theorem curl_grad_eq_zero (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (x : Space) :
    (∇ ⨯ (∇ f)) x = 0 :=
-- END SPEC
  sorry

end M182

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Component `i` of the left side is a difference of two mixed second partial derivatives of `f`
    (R11–R15 expose it). So first prove the milestone `mixed_partials`: `∂[i] (∂[j] f) x = ∂[j] (∂[i] f) x`.
H2. Milestone: rewrite each inner `∂[j] f` as the function `fun y => fderiv ℝ f y (basis j)` (R1), each
    outer `∂` with `Space.deriv_eq` (R2), and differentiate the application with `fderiv_clm_apply` (R3,
    side goals by `fun_prop`). The argument `basis j` is constant, so `simp` removes that term (R5–R7).
    Both sides become `fderiv ℝ (fderiv ℝ f) x (basis _) (basis _)`, which Schwarz (R8–R10) equates.
H3. Milestone ends with `exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _`. Main:
    `unfold Space.curl Space.grad; ext i; simp only [PiLp.zero_apply]; rw [mixed_partials f hf]; simp`.
-/

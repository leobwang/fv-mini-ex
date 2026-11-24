/- M184 | Curl of a rigid rotation | 15-20 min | ∇ ⨯, fin_cases, fderiv linearity, cross product, physlib
GOAL
  A body rotating rigidly with angular velocity `ω` has velocity field `v(y) = ω × y`. Show that its
  vorticity is twice the angular velocity: `∇ × v = 2ω` at every point `x`.

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.SpaceAndTime.Space.Derivatives.Curl

open Space Matrix

namespace M184

/- SKELETON · curl_rotation
  1. MILESTONE first: a helper theorem above `curl_rotation` (outside the spec), for the shape of every
     component of `ω × y`:
       deriv_lin (a b : ℝ) (j k l : Fin 3) (x : Space) :
         ∂[j] (fun y : Space => a * y.val k - b * y.val l) x =
           a * (if j = k then 1 else 0) - b * (if j = l then 1 else 0)
     ∂ → fderiv:                                                    R1
     split the difference (both side goals by R3):                  R2, R3
     pull out the constants, once per term (side goal by R3):       R4, R4
     apply the linear maps to `basis j` (R6, R7 once per term):     R5, R6, R7
     fold back to ∂ and evaluate ∂_j y_k (once per term):           R8, R9
     (R5–R9 also go as one `simp only [...]` with all five lemmas)
  2. Main proof. Vector equation → three component goals:            R10, R11
  3. In each component, one `simp` with `curl`, `cross_apply`, `basis_repr_apply` and the milestone
     `deriv_lin`; it applies, in this order:                        R12, R13, R14, R15, R16, R17,
                                                                     deriv_lin, R18, R19
  4. Close the leftover `ωᵢ + ωᵢ = 2 * ωᵢ`:                          R20
-/
-- BEGIN SPEC
theorem curl_rotation (ω : EuclideanSpace ℝ (Fin 3)) (x : Space) :
    (∇ ⨯ (fun y : Space => ω ⨯ₑ₃ basis.repr y)) x = (2 : ℝ) • ω :=
-- END SPEC
  sorry

end M184

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each component of `ω × y` has the form `a * y.val k - b * y.val l` with constants `a`, `b`. `simp` can
    unfold the curl and the cross product but cannot differentiate such a function (guide W2), so first
    prove its partial derivative once, as the milestone lemma `deriv_lin` of the SKELETON.
H2. Milestone: turn `∂[j]` into `fderiv` (R1), split with `fderiv_fun_sub` and `fderiv_const_mul`, each with
    `(by fun_prop)` arguments (R2–R4), then `simp only` the applied linear maps back into `∂[j]` of single
    coordinates (R5–R8) and finish with `deriv_component` (R9).
    Main: `ext i; fin_cases i`, then one `simp` with the definitions and `deriv_lin`, then `ring`.
H3. Milestone: `rw [Space.deriv_eq, fderiv_fun_sub (by fun_prop) (by fun_prop), fderiv_const_mul (by fun_prop),
    fderiv_const_mul (by fun_prop)]`, then one `simp only [...]` with the lemmas of R5–R9 (R8 written
    `← Space.deriv_eq`).
    Main: `fin_cases i <;> simp [curl, cross_apply, basis_repr_apply, deriv_lin] <;> ring`.
-/

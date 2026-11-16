/- M184 | Curl of a rigid rotation | 15-20 min | ∇ ⨯, fin_cases, fderiv linearity, cross product, physlib
GOAL
  A body rotating rigidly with angular velocity `ω` has velocity field `v(y) = ω × y`. Show that its
  vorticity is twice the angular velocity: `∇ × v = 2ω` at every point `x`.

REFERENCE
  `Space` is 3D space; `basis.repr y : EuclideanSpace ℝ (Fin 3)` is the point `y` as a coordinate vector.
  `a ⨯ₑ₃ b` is the cross product on `EuclideanSpace ℝ (Fin 3)` (needs `open Matrix`); `∇ ⨯ F` is `Space.curl F`.
  #check Space.curl  -- component i of (∇ ⨯ F) x is ∂[i+1] F_{i+2} - ∂[i+2] F_{i+1}  (`simp [curl]` unfolds)
  #check cross_apply -- a ⨯₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  #check Space.basis_repr_apply  -- (basis.repr p) i = p.val i
  #check Space.deriv_eq          -- ∂[μ] f x = fderiv ℝ f x (basis μ)   (partial → Fréchet derivative)
  #check fderiv_fun_sub          -- f, g differentiable at x → fderiv (fun y => f y - g y) x = fderiv f x - fderiv g x
  #check fderiv_const_mul        -- a differentiable at x → fderiv (fun y => b * a y) x = b • fderiv a x
  #check Space.deriv_component   -- ∂[ν] (fun x => x.val μ) x = if ν = μ then 1 else 0
  #check _root_.sub_apply        -- (f - g) v = f v - g v   (also `_root_.smul_apply`, `smul_eq_mul`)
  `ext i; fin_cases i` splits an equation in `EuclideanSpace ℝ (Fin 3)` into components `i = 0, 1, 2`;
  differentiability side goals such as `DifferentiableAt ℝ (fun y : Space => y.val k) x` go by `fun_prop`.
-/
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.SpaceAndTime.Space.Derivatives.Curl

open Space Matrix

namespace M184

-- BEGIN SPEC
theorem curl_rotation (ω : EuclideanSpace ℝ (Fin 3)) (x : Space) :
    (∇ ⨯ (fun y : Space => ω ⨯ₑ₃ basis.repr y)) x = (2 : ℝ) • ω :=
-- END SPEC
  sorry

end M184

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each component of `ω × y` has the form `a * y k - b * y l` with constants `a`, `b`. So first compute the
    partial derivative of such a function once and for all, as a helper lemma.
H2. Helper: `∂[j] (fun y : Space => a * y.val k - b * y.val l) x = a * (if j = k then 1 else 0) - b * (if j = l then 1 else 0)`.
    Prove it by `rw [Space.deriv_eq, fderiv_fun_sub .., fderiv_const_mul .., fderiv_const_mul ..]` and
    folding back with `← Space.deriv_eq`.
H3. Main: `ext i; fin_cases i <;> simp [curl, cross_apply, basis_repr_apply, helper] <;> ring`.
-/

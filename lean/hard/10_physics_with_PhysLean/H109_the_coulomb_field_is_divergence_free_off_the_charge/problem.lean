/- H109 | The Coulomb field is divergence free off the charge | 1.5-2 h | HasFDerivAt, chain rule, Space.div, norm calculus, physlib
GOAL
  The field of a point charge at the origin is `E(y) = y / ‖y‖³`. Prove Gauss's law away from the
  source, pointwise: `(∇ · E)(x) = 0` at every `x ≠ 0` (physlib only has the distributional version).

REFERENCE
  `Space` = 3D space; `x i` = coordinate `i` of `x`; `basis.repr y` = `y` as a vector in `EuclideanSpace ℝ (Fin 3)`.
  example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) : (∇ ⬝ F) x = ∑ i, ∂[i] (fun y => F y i) x := rfl
  example (f : Space → ℝ) (x : Space) (i : Fin 3) : ∂[i] f x = fderiv ℝ f x (basis i) := rfl  -- Space.deriv_eq
  #check Space.deriv_smul        -- c, f DifferentiableAt x → ∂[u] (c • f) x = c x • ∂[u] f x + ∂[u] c x • f x
  #check Space.deriv_component_same  -- ∂[i] (fun x => x i) x = 1;   Space.norm_sq_eq : ‖p‖ ^ 2 = ∑ i, p i ^ 2
  #check hasStrictFDerivAt_norm_sq   -- HasStrictFDerivAt (‖·‖ ^ 2) ((2 : ℕ) • innerSL ℝ x) x   (`.hasFDerivAt`)
                                     --   `innerSL ℝ x` = the linear map `y ↦ ⟪x, y⟫`; the `2` is a ℕ-scalar, write `(2 : ℕ)`
  #check HasFDerivAt.sqrt        -- HasFDerivAt f f' x → f x ≠ 0 → HasFDerivAt (√f ·) ((1 / (2 * √(f x))) • f') x   (√ = Real.sqrt)
  example (x : Space) (hx : x ≠ 0) : DifferentiableAt ℝ (‖·‖) x := DifferentiableAt.norm ℝ differentiableAt_id hx
  #check HasDerivAt.comp_hasFDerivAt  -- (g : ℝ → ℝ) has deriv g' at f x, f has fderiv f' → g ∘ f has fderiv g' • f'
  #check HasDerivAt.fun_inv      -- HasDerivAt c c' x → c x ≠ 0 → HasDerivAt (fun r => (c r)⁻¹) (-c' / c x ^ 2) x
  #check HasFDerivAt.fderiv      -- HasFDerivAt f f' x → fderiv 𝕜 f x = f'   (turn a derivative fact into a rewrite)
-/
import Physlib.SpaceAndTime.Space.Derivatives.Div

open Space InnerProductSpace

namespace H109

-- MILESTONE (optional: change or delete)
/-- `∂ᵢ ‖y‖ = xᵢ / ‖x‖` away from the origin. -/
theorem deriv_norm (i : Fin 3) (x : Space) (hx : x ≠ 0) :
    ∂[i] (fun y : Space => ‖y‖) x = x i / ‖x‖ := by
  sorry

-- MILESTONE (optional: change or delete)
/-- `∂ᵢ ‖y‖⁻³ = -3 xᵢ / ‖x‖⁵` away from the origin (chain rule through `r ↦ (r ^ 3)⁻¹`). -/
theorem deriv_inv_norm_cube (i : Fin 3) (x : Space) (hx : x ≠ 0) :
    ∂[i] (fun y : Space => (‖y‖ ^ 3)⁻¹) x = -3 * x i / ‖x‖ ^ 5 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- One summand of the divergence, by the product rule. -/
theorem deriv_summand (i : Fin 3) (x : Space) (hx : x ≠ 0) :
    ∂[i] (fun y : Space => (‖y‖ ^ 3)⁻¹ * y i) x = (‖x‖ ^ 3)⁻¹ - 3 * x i ^ 2 / ‖x‖ ^ 5 := by
  sorry

-- BEGIN SPEC
theorem coulomb_div_free (x : Space) (hx : x ≠ 0) :
    (∇ ⬝ (fun y : Space => (‖y‖ ^ 3)⁻¹ • basis.repr y)) x = 0 :=
-- END SPEC
  sorry

end H109

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each summand of the divergence is `∂ᵢ (yᵢ / ‖y‖³) = 1/‖x‖³ - 3 xᵢ² / ‖x‖⁵`. Summing over `i` and using
    `∑ xᵢ² = ‖x‖²` gives `3/‖x‖³ - 3/‖x‖³ = 0`. The work is the three derivative facts (the milestones),
    all valid only because `‖x‖ ≠ 0`: start every proof with `have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx`.
H2. `deriv_norm`: get `HasFDerivAt` for `‖y‖ ^ 2`, apply `.sqrt`, rewrite `√(‖y‖ ^ 2) = ‖y‖` inside the function
    (`funext`, `Real.sqrt_sq`), then `rw [Space.deriv_eq, h.fderiv]; simp [Real.sqrt_sq hn.le]; field_simp`. `deriv_inv_norm_cube`: chain rule with
    `g r = (r ^ 3)⁻¹`. `deriv_summand`: `change ∂[i] ((fun y => (‖y‖ ^ 3)⁻¹) • fun y => y i) x = _`, then
    `Space.deriv_smul`. Main: `unfold Space.div; simp only [PiLp.smul_apply, Space.basis_repr_apply, smul_eq_mul]`.
H3. Chain rule, stated so the function is the lambda you need:
    `have hcomp : HasFDerivAt (fun y : Space => (‖y‖ ^ 3)⁻¹) ((-(↑3 * ‖x‖ ^ 2) / (‖x‖ ^ 3) ^ 2) • fderiv ℝ (‖·‖) x) x :=
      ((hasDerivAt_pow 3 ‖x‖).fun_inv (by positivity)).comp_hasFDerivAt x hd.hasFDerivAt`.
    Finish the main theorem with `simp only [deriv_summand _ x hx, Fin.sum_univ_three]`, the three-term form of
    `Space.norm_sq_eq x`, `field_simp` and `nlinarith`.
-/

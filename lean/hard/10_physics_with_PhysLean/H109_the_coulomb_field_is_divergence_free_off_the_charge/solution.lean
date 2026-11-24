/- H109 | The Coulomb field is divergence free off the charge | 1.5-2 h | HasFDerivAt, chain rule, Space.div, norm calculus, physlib
GOAL
  The field of a point charge at the origin is `E(y) = y / ‖y‖³`. Prove Gauss's law away from the
  source, pointwise: `(∇ · E)(x) = 0` at every `x ≠ 0` (physlib only has the distributional version).

GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.SpaceAndTime.Space.Derivatives.Div

open Space InnerProductSpace

namespace H109

/- SKELETON · deriv_norm   (milestone 1: ∂ᵢ‖y‖ = xᵢ/‖x‖; used in milestone 2, step 6)
  Route: ‖y‖ = √(‖y‖ ^ 2), and ‖y‖ ^ 2 has a library derivative.
  1. hn : 0 < ‖x‖                                                           R1
  2. h1 : HasFDerivAt (fun y : Space => ‖y‖ ^ 2) ((2 : ℕ) • (innerSL ℝ) x) x  R3
  3. h2 : the derivative of `fun y => √(‖y‖ ^ 2)`; side goal by R2:          R4, R2
  4. Make h2 talk about `fun y => ‖y‖`:
       he : (fun y : Space => √(‖y‖ ^ 2)) = fun y => ‖y‖                    R5, R7 (R6)
       rewrite h2 with he                                                   R8
  5. Goal → the derivative map at `basis i` → the map from h2:              R9, R10
  6. Evaluate the map; `simp` with `Real.sqrt_sq hn.le`:                    simp (R11–R14, R7)
  7. Clear the denominators:                                                R15
-/
-- MILESTONE (optional: change or delete)
/-- `∂ᵢ ‖y‖ = xᵢ / ‖x‖` away from the origin. -/
theorem deriv_norm (i : Fin 3) (x : Space) (hx : x ≠ 0) :
    ∂[i] (fun y : Space => ‖y‖) x = x i / ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : HasFDerivAt (fun y : Space => ‖y‖ ^ 2) ((2 : ℕ) • (innerSL ℝ) x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := h1.sqrt (by positivity)
  -- WHY: `.sqrt` produces `√(‖y‖ ^ 2)`; rewrite it to `‖y‖` inside the function before using `.fderiv`.
  have he : (fun y : Space => √(‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [he] at h2
  rw [Space.deriv_eq, h2.fderiv]
  simp [Real.sqrt_sq hn.le]
  field_simp

/- SKELETON · deriv_inv_norm_cube   (milestone 2: ∂ᵢ‖y‖⁻³ = -3xᵢ/‖x‖⁵; uses milestone 1; used in milestone 3, step 5)
  Chain rule: outer g r = (r ^ 3)⁻¹ on ℝ, inner ‖·‖.
  1. hn : 0 < ‖x‖                                                           R1
  2. hd : DifferentiableAt ℝ (fun y : Space => ‖y‖) x                       R16
  3. hg : HasDerivAt (fun r : ℝ => (r ^ 3)⁻¹) (-(↑3 * ‖x‖ ^ 2) / (‖x‖ ^ 3) ^ 2) ‖x‖
                                                                            R17 → R18 (side goal R2)
  4. hcomp : HasFDerivAt (fun y : Space => (‖y‖ ^ 3)⁻¹)
               ((-(↑3 * ‖x‖ ^ 2) / (‖x‖ ^ 3) ^ 2) • fderiv ℝ (fun y : Space => ‖y‖) x) x
     state it with the lambda, prove it from hg and hd:                     R19, R20
  5. Goal → scalar * (fderiv ℝ (fun y => ‖y‖) x) (basis i):                 R9, R10, R11, R12
  6. Fold the second factor back into ∂[i], then milestone 1:               R9 backwards, rw [milestone 1]
  7. Clear the denominators:                                                R15
-/
-- MILESTONE (optional: change or delete)
/-- `∂ᵢ ‖y‖⁻³ = -3 xᵢ / ‖x‖⁵` away from the origin (chain rule through `r ↦ (r ^ 3)⁻¹`). -/
theorem deriv_inv_norm_cube (i : Fin 3) (x : Space) (hx : x ≠ 0) :
    ∂[i] (fun y : Space => (‖y‖ ^ 3)⁻¹) x = -3 * x i / ‖x‖ ^ 5 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd : DifferentiableAt ℝ (fun y : Space => ‖y‖) x :=
    DifferentiableAt.norm ℝ differentiableAt_id hx
  have hg : HasDerivAt (fun r : ℝ => (r ^ 3)⁻¹) (-(↑3 * ‖x‖ ^ 2) / (‖x‖ ^ 3) ^ 2) ‖x‖ :=
    (hasDerivAt_pow 3 ‖x‖).fun_inv (by positivity)
  -- WHY: state the composite as a lambda; `comp_hasFDerivAt` alone gives `g ∘ ‖·‖`, which `rw` won't match.
  have hcomp : HasFDerivAt (fun y : Space => (‖y‖ ^ 3)⁻¹)
      ((-(↑3 * ‖x‖ ^ 2) / (‖x‖ ^ 3) ^ 2) • fderiv ℝ (fun y : Space => ‖y‖) x) x :=
    hg.comp_hasFDerivAt x hd.hasFDerivAt
  rw [Space.deriv_eq, hcomp.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq, deriv_norm i x hx]
  field_simp

/- SKELETON · deriv_summand   (milestone 3: product rule; uses milestone 2; used in coulomb_div_free, step 4)
  1. hn, hd as in milestone 2:                                              R1, R16
  2. hc : DifferentiableAt ℝ (fun y : Space => (‖y‖ ^ 3)⁻¹) x                R22 (R21)
  3. hf : DifferentiableAt ℝ (fun y : Space => y i) x                        R23
  4. Restate the function as `(fun y => (‖y‖ ^ 3)⁻¹) • fun y => y i`:       R24
  5. Product rule, ∂ᵢ yᵢ = 1, then milestone 2:                              R25, R26, rw [milestone 2]
  6. `•` → `*` in both products at once: simp only [smul_eq_mul]          R12 via R31
     (`rw [smul_eq_mul]` changes only the first of the two `•`)
  7. Clear the denominators, finish:                                       R15, R27
-/
-- MILESTONE (optional: change or delete)
/-- One summand of the divergence, by the product rule. -/
theorem deriv_summand (i : Fin 3) (x : Space) (hx : x ≠ 0) :
    ∂[i] (fun y : Space => (‖y‖ ^ 3)⁻¹ * y i) x = (‖x‖ ^ 3)⁻¹ - 3 * x i ^ 2 / ‖x‖ ^ 5 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd : DifferentiableAt ℝ (fun y : Space => ‖y‖) x :=
    DifferentiableAt.norm ℝ differentiableAt_id hx
  have hc : DifferentiableAt ℝ (fun y : Space => (‖y‖ ^ 3)⁻¹) x :=
    (hd.pow 3).inv (pow_pos hn 3).ne'
  have hf : DifferentiableAt ℝ (fun y : Space => y i) x := by fun_prop
  change ∂[i] ((fun y : Space => (‖y‖ ^ 3)⁻¹) • fun y : Space => y i) x = _
  rw [Space.deriv_smul hc hf, deriv_component_same, deriv_inv_norm_cube i x hx]
  simp only [smul_eq_mul]
  field_simp
  ring

/- SKELETON · coulomb_div_free
  Prove the milestones first, in order 1 → 2 → 3; only milestone 3 is used here.
  1. hn : 0 < ‖x‖                                                           R1
  2. Divergence → ∑ i, ∂[i] (component i) x:                                R28
  3. Inside the sum, each component → `(‖y‖ ^ 3)⁻¹ * y i`:                  R31 with R29, R30, R12
  4. Substitute milestone 3 under the sum, expand the sum:                  R31 with milestone 3, R32
  5. h : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2                               R33, then R32 at h (R8)
  6. Clear the denominators, finish with h:                                 R15, R34
-/
-- BEGIN SPEC
theorem coulomb_div_free (x : Space) (hx : x ≠ 0) :
    (∇ ⬝ (fun y : Space => (‖y‖ ^ 3)⁻¹ • basis.repr y)) x = 0 :=
-- END SPEC
  by
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    unfold Space.div
    simp only [PiLp.smul_apply, basis_repr_apply, smul_eq_mul]
    simp only [deriv_summand _ x hx, Fin.sum_univ_three]
    have h := Space.norm_sq_eq x
    rw [Fin.sum_univ_three] at h
    field_simp
    nlinarith [h]

end H109

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each summand of the divergence is `∂ᵢ (yᵢ / ‖y‖³) = 1/‖x‖³ - 3 xᵢ² / ‖x‖⁵`; summing over `i` with
    `∑ xᵢ² = ‖x‖²` gives `3/‖x‖³ - 3/‖x‖³ = 0`. The work is the three derivative facts (the milestones, in
    order), all valid only because `‖x‖ ≠ 0`: start every proof with `have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx`.
H2. Milestone 1: `‖y‖ = √(‖y‖ ^ 2)`; take the derivative of `‖y‖ ^ 2` (`hasStrictFDerivAt_norm_sq`), apply
    `.sqrt`, rewrite `√(‖y‖ ^ 2)` to `‖y‖` inside the fact (`funext`, `Real.sqrt_sq`), then
    `rw [Space.deriv_eq, h2.fderiv]; simp [Real.sqrt_sq hn.le]; field_simp`. Milestone 2: chain rule with
    `g r = (r ^ 3)⁻¹` (`hasDerivAt_pow`, `.fun_inv`, `.comp_hasFDerivAt`), then `rw [← Space.deriv_eq]` and
    milestone 1. Milestone 3: `change` the function into `c • f`, then `Space.deriv_smul`,
    `Space.deriv_component_same` and milestone 2. Main: `unfold Space.div`, simplify the components, substitute
    milestone 3, expand with `Fin.sum_univ_three`, use `Space.norm_sq_eq x`.
H3. Chain rule, stated so the function is the lambda you need:
    `have hcomp : HasFDerivAt (fun y : Space => (‖y‖ ^ 3)⁻¹) ((-(↑3 * ‖x‖ ^ 2) / (‖x‖ ^ 3) ^ 2) • fderiv ℝ (fun y : Space => ‖y‖) x) x :=
      ((hasDerivAt_pow 3 ‖x‖).fun_inv (by positivity)).comp_hasFDerivAt x hd.hasFDerivAt`.
    Product rule: `change ∂[i] ((fun y : Space => (‖y‖ ^ 3)⁻¹) • fun y : Space => y i) x = _`.
    Main: `simp only [PiLp.smul_apply, Space.basis_repr_apply, smul_eq_mul]`, then
    `simp only [deriv_summand _ x hx, Fin.sum_univ_three]`, the three-term form of `Space.norm_sq_eq x`,
    `field_simp` and `nlinarith [h]`.
-/

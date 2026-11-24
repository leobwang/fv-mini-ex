/- H107 | Orthogonal null vectors are parallel | 45-60 min | lightlike vectors, norm of a difference, nlinarith, funext/match, physlib
GOAL
  A 4-vector `p` is null (lightlike) when `⟪p, p⟫ₘ = 0`. Show that two Minkowski-orthogonal null vectors are
  proportional: `⟪p, p⟫ₘ = ⟪q, q⟫ₘ = ⟪p, q⟫ₘ = 0` and `q ≠ 0` give `p = r • q` for some real `r`.

REFERENCE
  `Lorentz.Vector d = (Fin 1 ⊕ Fin d → ℝ)`; `⟪p, q⟫ₘ = p⁰ q⁰ - p⃗ · q⃗` (scoped: `open Lorentz Vector`).
  `p.timeComponent = p (Sum.inl 0)` is `p⁰`; `p.spatialPart : EuclideanSpace ℝ (Fin d)` is `p⃗`.
  #check Lorentz.Vector.minkowskiProduct_eq_timeComponent_spatialPart  -- ⟪p, q⟫ₘ = p⁰ * q⁰ - inner ℝ p⃗ q⃗
  #check Lorentz.Vector.minkowskiProduct_self_eq_timeComponent_spatialPart  -- ⟪p, p⟫ₘ = ‖p⁰‖^2 - ‖p⃗‖^2
  #check norm_sub_sq_real      -- ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2
  #check real_inner_smul_left  -- inner ℝ (r • x) y = r * inner ℝ x y   (and `real_inner_smul_right`)
  #check norm_smul             -- ‖r • x‖ = ‖r‖ * ‖x‖
  #check smul_smul             -- a • b • x = (a * b) • x   (bare `mul_smul` is ambiguous after the `open`)
  example {d : ℕ} (r : ℝ) (q : Lorentz.Vector d) : (r • q).spatialPart = r • q.spatialPart := rfl
  `funext μ; match μ with | Sum.inl 0 => _ | Sum.inr i => _` proves a 4-vector equation by components.
NOTE: the `_self_` lemma writes `p⁰²` as `‖p⁰‖ ^ 2`; `simp only [Real.norm_eq_abs, sq_abs] at h` clears it.
-/
import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

open Lorentz Vector

namespace H107

-- MILESTONE (optional: change or delete)
/-- A nonzero null vector has a nonzero time component. -/
theorem time_ne_zero_of_null {d : ℕ} (q : Lorentz.Vector d) (hq : ⟪q, q⟫ₘ = 0) (hq0 : q ≠ 0) :
    q.timeComponent ≠ 0 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- The key identity: `q⁰ p⃗ - p⁰ q⃗` has zero length. -/
theorem key {d : ℕ} (p q : Lorentz.Vector d) (hp : ⟪p, p⟫ₘ = 0) (hq : ⟪q, q⟫ₘ = 0)
    (hpq : ⟪p, q⟫ₘ = 0) :
    ‖q.timeComponent • p.spatialPart - p.timeComponent • q.spatialPart‖ ^ 2 = 0 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- A 4-vector is determined by its time component and its spatial part. -/
theorem ext_time_space {d : ℕ} (p q : Lorentz.Vector d) (h0 : p.timeComponent = q.timeComponent)
    (hs : p.spatialPart = q.spatialPart) : p = q := by
  sorry

-- BEGIN SPEC
theorem parallel_of_null_orth {d : ℕ} (p q : Lorentz.Vector d) (hp : ⟪p, p⟫ₘ = 0)
    (hq : ⟪q, q⟫ₘ = 0) (hq0 : q ≠ 0) (hpq : ⟪p, q⟫ₘ = 0) : ∃ r : ℝ, p = r • q :=
-- END SPEC
  sorry

end H107

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `a = p⁰`, `b = q⁰`. The hypotheses say `a² = ‖p⃗‖²`, `b² = ‖q⃗‖²` and `a b = p⃗ · q⃗`. The candidate
    is `r = a / b`, which needs `b ≠ 0` (if `q⁰ = 0` then `‖q⃗‖ = 0`, so `q = 0`).
H2. Expand `‖b • p⃗ - a • q⃗‖² = b²‖p⃗‖² - 2ab (p⃗ · q⃗) + a²‖q⃗‖² = a²b² - 2a²b² + a²b² = 0`, so `b • p⃗ = a • q⃗`.
    Then compare `p` and `(a / b) • q` separately in time and in space.
H3. `key`: `rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]`, normalize
    with `simp only [Real.norm_eq_abs, mul_pow, sq_abs]`, substitute `inner ℝ p⃗ q⃗ = a * b`, then `nlinarith`.
    Main: `rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h`, `refine ⟨a / b, ext_time_space _ _ ?_ ?_⟩`;
    the space part is `rw [div_eq_inv_mul, ← smul_smul, ← h, smul_smul, inv_mul_cancel₀ hb, one_smul]` after a `change`.
-/

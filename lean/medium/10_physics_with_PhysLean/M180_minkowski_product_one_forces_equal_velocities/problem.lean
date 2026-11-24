/- M180 | ⟪u, v⟫ₘ = 1 forces equal 4-velocities | 15-20 min | Velocity subtype, Cauchy–Schwarz, timelike vs null, funext/match, physlib
GOAL
  A 4-velocity `u : Velocity d` is a vector with `⟪u, u⟫ₘ = 1` and time component `u⁰ > 0`. The relative
  Lorentz factor of two 4-velocities is `⟪u, v⟫ₘ`. Show that it equals 1 only when `u = v`.

REFERENCE
  `Lorentz.Vector d = (Fin 1 ⊕ Fin d → ℝ)`; `⟪p, q⟫ₘ = p⁰ q⁰ - p⃗ · q⃗` (scoped: `open Lorentz Vector`).
  `p.timeComponent = p (Sum.inl 0)` is `p⁰`; `p.spatialPart : EuclideanSpace ℝ (Fin d)` is `p⃗`.
  `Velocity d` is a `Set (Lorentz.Vector d)`, so `u : Velocity d` is a subtype element and `u.1` its vector.
  #check Lorentz.Velocity.ext   -- u.1 = v.1 → u = v   (`ext1` applies it)
  example {d : ℕ} (u : Velocity d) : ⟪u.1, u.1⟫ₘ = 1 := by simp
  #check Lorentz.Vector.minkowskiProduct_eq_timeComponent_spatialPart  -- ⟪p, q⟫ₘ = p⁰ * q⁰ - inner ℝ p⃗ q⃗
  #check Lorentz.Vector.minkowskiProduct_self_eq_timeComponent_spatialPart  -- ⟪p, p⟫ₘ = ‖p⁰‖^2 - ‖p⃗‖^2
  #check abs_real_inner_le_norm  -- |inner ℝ x y| ≤ ‖x‖ * ‖y‖   (Cauchy–Schwarz)
  #check sq_le_sq'               -- -b ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2
  `⟪·,·⟫ₘ` is bilinear: `simp [map_sub, minkowskiProduct_symm v.1 u.1]` expands `⟪u.1 - v.1, u.1 - v.1⟫ₘ`.
  `funext μ; match μ with | Sum.inl 0 => _ | Sum.inr i => _` proves a 4-vector equation by components.
-/
import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

open Lorentz Vector

namespace M180

-- MILESTONE (optional: change or delete)
/-- A vector that is null and Minkowski-orthogonal to a timelike vector is zero. -/
theorem eq_zero_of_orth {d : ℕ} (u w : Lorentz.Vector d) (hu : 0 < ⟪u, u⟫ₘ)
    (hw : ⟪w, w⟫ₘ = 0) (huw : ⟪u, w⟫ₘ = 0) : w = 0 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at hu hw
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at huw
  simp only [Real.norm_eq_abs, sq_abs] at hu hw
  -- now hu : 0 < u⁰ ^ 2 - ‖u⃗‖ ^ 2,  hw : w⁰ ^ 2 - ‖w⃗‖ ^ 2 = 0,  huw : u⁰ * w⁰ - inner ℝ u⃗ w⃗ = 0
  sorry

-- BEGIN SPEC
theorem eq_of_minkowskiProduct_eq_one {d : ℕ} (u v : Velocity d) (h : ⟪u.1, v.1⟫ₘ = 1) :
    u = v :=
-- END SPEC
  sorry

end M180

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Look at `w = u.1 - v.1`. Expand `⟪w, w⟫ₘ` and `⟪u.1, w⟫ₘ` with bilinearity: both are `0`.
H2. Milestone: write everything in `(w⁰, w⃗)` form. If `w⁰ ≠ 0`, then `u⁰ w⁰ = inner ℝ u⃗ w⃗` and Cauchy–Schwarz
    give `(u⁰ w⁰)² ≤ ‖u⃗‖² ‖w⃗‖² = ‖u⃗‖² (w⁰)² < (u⁰)² (w⁰)²`, a contradiction (`nlinarith`). So `w⁰ = 0`,
    hence `‖w⃗‖² = 0` and `w⃗ = 0`; finish by components.
H3. Main: `have hw := eq_zero_of_orth u.1 (u.1 - v.1) (by simp) (by simp [map_sub, minkowskiProduct_symm v.1 u.1, h])
    (by simp [map_sub, h])`, then `ext1; exact sub_eq_zero.mp hw`. Milestone key step: `have hw0 : w.timeComponent = 0`
    by `by_contra h0`, squaring Cauchy–Schwarz with `sq_le_sq'` (rewrite `u⁰ * w⁰` as the inner product), then `nlinarith`.
-/

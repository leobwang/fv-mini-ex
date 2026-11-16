/- M185 | Energy of the oscillator trajectory | 15-20 min | inner products, norm_smul, sin²+cos², linear_combination, physlib
GOAL
  physlib solves the harmonic oscillator explicitly: `x(t) = cos(ωt) x₀ + (sin(ωt)/ω) v₀`. By direct
  computation, show that its energy at every time `t` is `½ (m ‖v₀‖² + k ‖x₀‖²)`.

REFERENCE
  `S : HarmonicOscillator` has mass `S.m > 0`, spring constant `S.k > 0` and `S.ω = √(k/m)`. Positions lie in
  `EuclideanSpace ℝ (Fin 1)` (ℝ¹ with `⟪x, y⟫_ℝ`, `‖x‖`); `t : Time` wraps a real `t.val`; `∂ₜ x t` is the velocity.
  `S.energy x t = 1/2 * S.m * ⟪∂ₜ x t, ∂ₜ x t⟫_ℝ + (1/2 : ℝ) • S.k • ⟪x t, x t⟫_ℝ` (defs `energy`, `kineticEnergy`, `potentialEnergy`).
  #check InitialConditions.trajectory_eq        -- IC.trajectory S = fun t => cos (ω t) • x₀ + (sin (ω t) / ω) • v₀
  #check InitialConditions.trajectory_velocity  -- ∂ₜ (IC.trajectory S) = fun t => -ω • sin (ω t) • x₀ + cos (ω t) • v₀
  #check HarmonicOscillator.ω_sq          -- S.ω ^ 2 = S.k / S.m   (also `ω_ne_zero`, `m_ne_zero`)
  #check real_inner_self_eq_norm_sq       -- ⟪x, x⟫_ℝ = ‖x‖ ^ 2
  #check real_inner_smul_left             -- ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ  (also `_right`, `inner_add_left/right`, `real_inner_comm`)
  #check Real.sin_sq_add_cos_sq           -- sin x ^ 2 + cos x ^ 2 = 1
  `linear_combination e * h` closes `a = b` when `a - b - e * (h.lhs - h.rhs)` is `0` by `ring`.
NOTE: rewrite `∂ₜ (IC.trajectory S)` with `trajectory_velocity` before unfolding `IC.trajectory S` with `trajectory_eq`.
BANNED: trajectory_energy, energy_conservation_of_equationOfMotion, energy_conservation_of_equationOfMotion', exact?, apply?, rw?, hint, observe, try?
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time Real InnerProductSpace

namespace M185

-- BEGIN SPEC
theorem energy_along_trajectory (S : HarmonicOscillator) (IC : InitialConditions) (t : Time) :
    S.energy (IC.trajectory S) t = 1/2 * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2) :=
-- END SPEC
  by
    have hk : S.k = S.m * S.ω ^ 2 := by
      rw [ω_sq]
      field_simp [S.m_ne_zero]
    simp only [energy, kineticEnergy, potentialEnergy]
    -- WHY: `trajectory_velocity` is stated for `∂ₜ (IC.trajectory S)`; unfolding the trajectory first
    -- would leave a derivative of an explicit function that it no longer matches.
    rw [InitialConditions.trajectory_velocity]
    simp only [InitialConditions.trajectory_eq, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, smul_eq_mul, real_inner_comm IC.x₀ IC.v₀]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    rw [hk]
    field_simp [S.ω_ne_zero]
    linear_combination (‖IC.v₀‖ ^ 2 + S.ω ^ 2 * ‖IC.x₀‖ ^ 2) * Real.sin_sq_add_cos_sq (S.ω * t.val)

end M185

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold the energy, substitute the velocity and the trajectory, and expand all inner products into
    `‖x₀‖²`, `‖v₀‖²` and `⟪x₀, v₀⟫_ℝ`. The cross terms cancel; what remains is `sin² + cos² = 1`.
H2. Replace `S.k` by `S.m * S.ω ^ 2` first (from `ω_sq` and `m_ne_zero`), so that `field_simp` can clear the
    `1 / ω` in the trajectory. Use `real_inner_comm IC.x₀ IC.v₀` to merge the two cross terms.
H3. After `simp only [energy, kineticEnergy, potentialEnergy]`, `rw [InitialConditions.trajectory_velocity]` and
    expanding (`simp only [trajectory_eq, inner_add_left, inner_add_right, real_inner_smul_left, ...]`; turn
    `⟪x₀, x₀⟫_ℝ` into `‖x₀‖ ^ 2` only afterwards), `rw [hk]`, `field_simp`, then
    `linear_combination (_) * Real.sin_sq_add_cos_sq (S.ω * t.val)`: find the coefficient `(_)` from the goal.
-/

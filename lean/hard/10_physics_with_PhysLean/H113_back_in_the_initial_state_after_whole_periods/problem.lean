/- H113 | Back in the initial state exactly after whole periods | 1-1.5 h | trigonometry, inner products, Real.cos_eq_one_iff, iff, physlib
GOAL
  A non-trivial oscillator (`x₀ ≠ 0` or `v₀ ≠ 0`) is back at its initial position **and** velocity at time `t`
  if and only if `t` is an integer multiple of the period `2π/ω`.

REFERENCE
  `S : HarmonicOscillator` has `S.m, S.k > 0` and `S.ω = √(k/m)`; `t : Time` wraps a real `t.val`; `∂ₜ x t` = velocity.
  #check InitialConditions.trajectory_eq        -- IC.trajectory S = fun t => cos (ω t) • x₀ + (sin (ω t) / ω) • v₀
  #check InitialConditions.trajectory_velocity  -- ∂ₜ (IC.trajectory S) = fun t => -ω • sin (ω t) • x₀ + cos (ω t) • v₀
  #check Real.cos_eq_one_iff   -- cos x = 1 ↔ ∃ n : ℤ, ↑n * (2 * π) = x
  #check Real.sin_int_mul_pi   -- sin (↑n * π) = 0
  #check real_inner_self_pos   -- 0 < ⟪x, x⟫_ℝ ↔ x ≠ 0   (also `real_inner_self_nonneg`)
  #check real_inner_smul_right -- ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ  (also `inner_add_right`, `real_inner_comm`)
  #check HarmonicOscillator.ω_ne_zero  -- S.ω ≠ 0   (also `ω_pos`)
  example (a b : EuclideanSpace ℝ (Fin 1)) (h : a = b) : ⟪a, a⟫_ℝ = ⟪a, b⟫_ℝ := congrArg (fun w => ⟪a, w⟫_ℝ) h
  `field_simp` clears `/ S.ω` given `S.ω ≠ 0` in context; `linear_combination e₁ * h₁ + h₂` closes the rest by `ring`.
BANNED: HarmonicOscillator.return_time, HarmonicOscillator.trajectory_periodic, exact?, apply?, try?, hint
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time Real InnerProductSpace

namespace H113

-- MILESTONE (optional: change or delete)
/-- A non-trivial initial state has positive "energy-like" quantity `‖v₀‖² + ω²‖x₀‖²`. -/
theorem det_pos (S : HarmonicOscillator) (IC : InitialConditions)
    (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) :
    0 < ⟪IC.v₀, IC.v₀⟫_ℝ + S.ω ^ 2 * ⟪IC.x₀, IC.x₀⟫_ℝ := by
  sorry

-- MILESTONE (optional: change or delete)
/-- Returning to the initial state forces `cos (ω t) = 1`. -/
theorem cos_eq_one (S : HarmonicOscillator) (IC : InitialConditions)
    (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) (t : Time)
    (hx : IC.trajectory S t = IC.x₀) (hv : ∂ₜ (IC.trajectory S) t = IC.v₀) :
    Real.cos (S.ω * t.val) = 1 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- The (←) direction: after `n` whole periods the state is the initial one. -/
theorem state_at_period (S : HarmonicOscillator) (IC : InitialConditions) (t : Time) (n : ℤ)
    (hn : (n : ℝ) * (2 * π / S.ω) = t.val) :
    IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀ := by
  sorry

-- BEGIN SPEC
theorem returns_iff_whole_periods (S : HarmonicOscillator) (IC : InitialConditions)
    (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) (t : Time) :
    (IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀) ↔
      ∃ n : ℤ, (n : ℝ) * (2 * π / S.ω) = t.val :=
-- END SPEC
  sorry

end H113

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (←) is direct: `ω t = 2nπ`, so `cos = 1` and `sin = 0`, and the formulas collapse. (→) is the real work: pair the
    position equation with `x₀` and the velocity equation with `v₀` to get two scalar equations in `c = cos ωt`,
    `s = sin ωt`, `xx = ⟪x₀,x₀⟫`, `vv = ⟪v₀,v₀⟫`, `xv = ⟪x₀,v₀⟫`.
H2. The scalar equations are `c·xx + (s/ω)·xv = xx` and `−ω·s·xv + c·vv = vv`. Multiply the first by `ω²`
    (after clearing `/ω`) and add: the `s·xv` terms cancel, leaving `(vv + ω²·xx)(c − 1) = 0`; `det_pos` rules out the
    first factor. For `det_pos`, split `non_trivial` and use `nlinarith` with `real_inner_self_pos.mpr h`.
H3. `cos_eq_one`: after `rw [trajectory_eq] at hx`, `rw [trajectory_velocity] at hv`, the `congrArg` pairings and
    `simp only [inner_add_right, real_inner_smul_right] at h1 h2`, `rw [real_inner_comm IC.x₀ IC.v₀] at h2`,
    `field_simp at h1`, prove `key : (vv + ω²·xx) * (cos (S.ω * t.val) - 1) = 0 := by linear_combination S.ω * h1 + h2`.
    (←): `have : S.ω * t.val = (2 * n : ℤ) * π := by rw [← hn]; push_cast; field_simp [S.ω_ne_zero]`.
-/

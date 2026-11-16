/- H112 | Uniqueness of oscillator trajectories | 1-1.5 h | linearity of the EOM, energy method, Time.deriv, physlib
GOAL
  A smooth solution `x` of the harmonic oscillator's equation of motion with initial position `IC.x₀` and initial
  velocity `IC.v₀` is physlib's explicit trajectory `IC.trajectory S`. Use the energy method on `y = x − trajectory`.

REFERENCE
  `S : HarmonicOscillator` (mass `S.m > 0`, spring constant `S.k > 0`); positions lie in `EuclideanSpace ℝ (Fin 1)`;
  `t : Time`; `∂ₜ x t` = velocity; `ContDiff ℝ ∞ x` = smooth; `S.EquationOfMotion x` is defined variationally.
  `S.energy y t = S.kineticEnergy y t + S.potentialEnergy (y t) = 1/2 * S.m * ⟪∂ₜ y t, ∂ₜ y t⟫_ℝ + (1/2) • S.k • ⟪y t, y t⟫_ℝ`
  #check HarmonicOscillator.equationOfMotion_iff_newtons_2nd_law  -- smooth x → (EOM ↔ ∀ t, S.m • ∂ₜ (∂ₜ x) t = S.force (x t))
  #check HarmonicOscillator.force_eq_linear                       -- S.force x = -S.k • x
  #check HarmonicOscillator.energy_conservation_of_equationOfMotion'  -- smooth + EOM → S.energy x t = S.energy x 0
  #check InitialConditions.trajectory_equationOfMotion  -- the trajectory solves the EOM (smooth: `by fun_prop`)
  #check Time.deriv_eq              -- ∂ₜ f t = fderiv ℝ f t 1;  then `fderiv_fun_sub hf hg` splits a difference
  #check Time.deriv_differentiable_of_contDiff  -- ContDiff ℝ ∞ f → Differentiable ℝ (∂ₜ f)
  #check add_eq_zero_iff_of_nonneg  -- 0 ≤ a → 0 ≤ b → (a + b = 0 ↔ a = 0 ∧ b = 0);  also `inner_self_eq_zero`
  `hx.differentiable (by simp) : Differentiable ℝ x` from `hx : ContDiff ℝ ∞ x`; `hx.sub hT` is smoothness of `x - T`.
BANNED: InitialConditions.trajectories_unique, ClassicalMechanics.DampedHarmonicOscillator.trajectories_unique, exact?, apply?, try?, hint
BANNED: ClassicalMechanics.DampedHarmonicOscillator.equationOfMotion_unique, ClassicalMechanics.DampedHarmonicOscillator.toUndamped_equationOfMotion
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time ContDiff InnerProductSpace

namespace H112

-- MILESTONE (optional: change or delete)
/-- `∂ₜ` of a difference of differentiable paths. -/
theorem deriv_sub (f g : Time → EuclideanSpace ℝ (Fin 1)) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) : ∂ₜ (fun t => f t - g t) = fun t => ∂ₜ f t - ∂ₜ g t := by
  sorry

-- MILESTONE (optional: change or delete)
/-- The equation of motion is linear: the difference of two solutions is a solution. -/
theorem eom_sub (S : HarmonicOscillator) (IC : InitialConditions)
    (x : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x) :
    S.EquationOfMotion (fun t => x t - IC.trajectory S t) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- A path whose energy vanishes at all times is identically zero. -/
theorem eq_zero_of_energy_zero (S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hE : ∀ t, S.energy y t = 0) : y = 0 := by
  sorry

-- BEGIN SPEC
theorem trajectory_unique (S : HarmonicOscillator) (IC : InitialConditions)
    (x : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x)
    (h0 : x 0 = IC.x₀) (hv : ∂ₜ x 0 = IC.v₀) :
    x = IC.trajectory S :=
-- END SPEC
  sorry

end H112

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Set `y := fun t => x t - IC.trajectory S t`. It solves the EOM (linearity), starts at rest at the origin, so its
    energy is `0` at time `0`; conservation makes it `0` forever, and zero energy forces `y = 0`.
H2. Linearity goes through Newton's law: rewrite both EOMs with `equationOfMotion_iff_newtons_2nd_law`, split
    `∂ₜ (∂ₜ y)` with `deriv_sub` twice, then `smul_sub` and `force_eq_linear`. For zero energy, both energy terms are
    `≥ 0` (`mul_nonneg`, `smul_nonneg`, `real_inner_self_nonneg`), so the potential term is `0`, so `⟪y t, y t⟫_ℝ = 0`.
H3. `deriv_sub`: `funext t; simp only [Time.deriv_eq, fderiv_fun_sub (hf t) (hg t), sub_apply]`.
    Main: `rw [S.energy_conservation_of_equationOfMotion' y (hx.sub hT) (eom_sub S IC x hx h)]`, then
    `simp [energy, kineticEnergy, potentialEnergy, hv0, hy0]` with `hv0 : ∂ₜ y 0 = 0`, `hy0 : y 0 = 0`; finish with
    `sub_eq_zero.mp (congrFun (eq_zero_of_energy_zero S y hE) t)`.
-/

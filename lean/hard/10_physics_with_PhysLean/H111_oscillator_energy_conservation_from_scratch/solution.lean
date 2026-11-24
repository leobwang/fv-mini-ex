/- H111 | Oscillator energy conservation from scratch | 1-1.5 h | Time.deriv, fderiv of inner products, is_const_of_fderiv_eq_zero, physlib
GOAL
  physlib defines the harmonic oscillator's equation of motion variationally (Euler–Lagrange). Prove that every
  smooth solution conserves `E = ½ m ‖ẋ‖² + ½ k ‖x‖²`: compute `dE/dt` yourself, then show `E` is constant.

REFERENCE
  `S.m`, `S.k` = mass, spring constant (fields of `S : HarmonicOscillator`; `S.m_pos : 0 < S.m`, `S.k_pos : 0 < S.k`).
  `Time` wraps ℝ (`t.val`); `∂ₜ f t = fderiv ℝ f t 1` (`Time.deriv_eq`); `x t : EuclideanSpace ℝ (Fin 1)`; `ContDiff ℝ ∞ x` = smooth.
  #check kineticEnergy_eq      -- S.kineticEnergy x = fun t => 1 / 2 * S.m * ⟪∂ₜ x t, ∂ₜ x t⟫_ℝ   (also potentialEnergy_eq, energy_eq)
  #check equationOfMotion_iff_newtons_2nd_law  -- EOM ↔ ∀ t, S.m • ∂ₜ (∂ₜ x) t = S.force (x t);  force_eq_linear : S.force x = -S.k • x
  #check Time.deriv_differentiable_of_contDiff  -- ContDiff ℝ ∞ f → Differentiable ℝ (∂ₜ f)
  #check potentialEnergy_differentiable  -- also kineticEnergy_ / energy_differentiable (all `fun_prop` lemmas)
  #check fderiv_inner_apply    -- (explicit ℝ) fderiv (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv g x y⟫ + ⟪fderiv f x y, g x⟫
  #check fderiv_const_mul      -- DifferentiableAt a x → fderiv (fun y => b * a y) x = b • fderiv a x
  #check fderiv_fun_add        -- f, g DifferentiableAt → fderiv (fun y => f y + g y) x = fderiv f x + fderiv g x
  #check inner_smul_right      -- ⟪x, r • y⟫ = r * ⟪x, y⟫;   real_inner_comm x y : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ
  #check is_const_of_fderiv_eq_zero  -- Differentiable f → (∀ x, fderiv 𝕜 f x = 0) → ∀ x y, f x = f y
  #check Time.eq_one_smul      -- t = t.val • 1   (so a linear map on `Time` is zero once it kills `1`)
BANNED: energy_conservation_of_equationOfMotion, energy_conservation_of_equationOfMotion', energy_deriv, kineticEnergy_deriv, potentialEnergy_deriv, trajectories_unique, trajectory_energy, ClassicalMechanics.DampedHarmonicOscillator.energy_dissipation_rate, ClassicalMechanics.DampedHarmonicOscillator.toUndamped_equationOfMotion, exact?, apply?, rw?, try?, hint, observe
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

open ClassicalMechanics HarmonicOscillator Time ContDiff InnerProductSpace

namespace H111

-- MILESTONE (optional: change or delete)
/-- `d/dt (½ m ⟪ẋ, ẋ⟫) = ⟪ẋ, m ẍ⟫`. -/
theorem kinetic_deriv (S : HarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) :
    ∂ₜ (S.kineticEnergy x) = fun t => ⟪∂ₜ x t, S.m • ∂ₜ (∂ₜ x) t⟫_ℝ := by
  funext t
  have hd : DifferentiableAt ℝ (∂ₜ x) t :=
    (Time.deriv_differentiable_of_contDiff x hx).differentiableAt
  rw [kineticEnergy_eq, Time.deriv_eq, fderiv_const_mul (by fun_prop), _root_.smul_apply,
    fderiv_inner_apply ℝ hd hd, ← Time.deriv_eq, inner_smul_right, real_inner_comm (∂ₜ x t)]
  ring

-- MILESTONE (optional: change or delete)
/-- `d/dt (½ k ⟪x, x⟫) = ⟪ẋ, k x⟫`. -/
theorem potential_deriv (S : HarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) :
    ∂ₜ (fun t => S.potentialEnergy (x t)) = fun t => ⟪∂ₜ x t, S.k • x t⟫_ℝ := by
  funext t
  have hd : DifferentiableAt ℝ x t := (hx.differentiable (by simp)).differentiableAt
  -- WHY: `potentialEnergy` is written with `•` on reals; turn it into `*` so `fderiv_const_mul` matches.
  simp only [potentialEnergy_eq, smul_eq_mul, ← mul_assoc]
  rw [Time.deriv_eq, fderiv_const_mul (by fun_prop), _root_.smul_apply,
    fderiv_inner_apply ℝ hd hd, ← Time.deriv_eq, inner_smul_right, real_inner_comm (x t)]
  ring

-- MILESTONE (optional: change or delete)
theorem energy_deriv_zero (S : HarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x) : ∂ₜ (S.energy x) = 0 := by
  rw [equationOfMotion_iff_newtons_2nd_law S x hx] at h
  funext t
  have hd : DifferentiableAt ℝ (fun t => S.potentialEnergy (x t)) t :=
    S.potentialEnergy_differentiable x hx t
  rw [energy_eq, Time.deriv_eq, fderiv_fun_add (by fun_prop) hd, _root_.add_apply, ← Time.deriv_eq,
    ← Time.deriv_eq, kinetic_deriv S x hx, potential_deriv S x hx, ← inner_add_right, h t,
    force_eq_linear]
  simp

-- BEGIN SPEC
theorem energy_const (S : HarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x) (t : Time) :
    S.energy x t = S.energy x 0 :=
-- END SPEC
  by
    apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (by fun_prop)
    intro τ
    -- WHY: `fderiv ℝ f τ : Time →L[ℝ] ℝ` is determined by its value at `1`, which is `∂ₜ f τ`.
    ext p
    rw [p.eq_one_smul, map_smul, ← Time.deriv_eq, energy_deriv_zero S x hx h]
    simp

end H111

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `dE/dt = ⟪ẋ, m ẍ⟫ + ⟪ẋ, k x⟫ = ⟪ẋ, m ẍ + k x⟫`, and Newton's law (from the equation of motion) says
    `m ẍ = -k x`, so `dE/dt = 0`. A function `Time → ℝ` with zero derivative everywhere is constant.
H2. Each energy derivative: `funext t`, unfold with `kineticEnergy_eq` / `potentialEnergy_eq` (turn `•` on reals into `*`
    with `smul_eq_mul`), `rw [Time.deriv_eq, fderiv_const_mul _, _root_.smul_apply, fderiv_inner_apply ℝ hd hd, ← Time.deriv_eq]`,
    then collect the two equal inner products with `inner_smul_right`, `real_inner_comm` and `ring`.
    Sum: `fderiv_fun_add`, then `← inner_add_right`, Newton and `force_eq_linear`.
H3. Constancy: `apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (by fun_prop)`, `intro τ; ext p`, then
    `rw [p.eq_one_smul, map_smul, ← Time.deriv_eq, energy_deriv_zero S x hx h]; simp`.
    For the kinetic part you need `hd : DifferentiableAt ℝ (∂ₜ x) t := (Time.deriv_differentiable_of_contDiff x hx).differentiableAt`.
-/

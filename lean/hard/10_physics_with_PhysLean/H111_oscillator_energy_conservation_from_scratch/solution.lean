/- H111 | Oscillator energy conservation from scratch | 1-1.5 h | Time.deriv, fderiv of inner products, is_const_of_fderiv_eq_zero, physlib
GOAL
  physlib defines the harmonic oscillator's equation of motion variationally (Euler–Lagrange). Prove that every
  smooth solution conserves `E = ½ m ‖ẋ‖² + ½ k ‖x‖²`: compute `dE/dt` yourself, then show `E` is constant.
BANNED: energy_conservation_of_equationOfMotion, energy_conservation_of_equationOfMotion', energy_deriv, kineticEnergy_deriv, potentialEnergy_deriv, trajectories_unique, trajectory_energy, ClassicalMechanics.DampedHarmonicOscillator.energy_dissipation_rate, ClassicalMechanics.DampedHarmonicOscillator.toUndamped_equationOfMotion, exact?, apply?, rw?, try?, hint, observe

GUIDE
  Entries R1–R31: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

open ClassicalMechanics HarmonicOscillator Time ContDiff InnerProductSpace

namespace H111

/- SKELETON · kinetic_deriv   (milestone 1: dT/dt = ⟪ẋ, m ẍ⟫; used in milestone 3)
  1. Pointwise:                                                              R1
  2. hd : DifferentiableAt ℝ (∂ₜ x) t   (velocity is differentiable):        R2, R3
  3. Unfold `T`, then `∂ₜ` → derivative map applied to `1`:                  R4, R5
  4. Constant `1 / 2 * S.m` out (side argument `by fun_prop`), evaluate:     R7 (R6), R8
  5. Product rule with `hd hd`, then fold back into `∂ₜ`:                    R9, R5 backwards
  6. Right side `⟪ẋ, m • ẍ⟫` → `m * ⟪ẋ, ẍ⟫`; make the two products equal:    R10, R11
  7. Close `(1 / 2 * m) • (a + a) = m * a`:                                  R12
-/
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

/- SKELETON · potential_deriv   (milestone 2: dU/dt = ⟪ẋ, k x⟫; used in milestone 3)
  Same route as milestone 1; only steps 2 and 3 differ.
  1. Pointwise:                                                              R1
  2. hd : DifferentiableAt ℝ x t:                                            R13, R3
  3. Unfold `U` under the `fun`, turn `•` into `*`, regroup to `b * a y`
     (one `simp only`):                                                      R14, R15, R16
  4. Then exactly steps 3–7 of milestone 1 (without R4):                     R5, R7 (R6), R8, R9,
                                                                             R5 backwards, R10, R11, R12
-/
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

/- SKELETON · energy_deriv_zero   (milestone 3: dE/dt = 0; used in energy_const)
  Prove milestones 1 and 2 first; they are used in step 5.
  1. Equation of motion → Newton's law in `h`:                               R17
  2. Pointwise:                                                              R1
  3. hd : DifferentiableAt ℝ (fun t => S.potentialEnergy (x t)) t:           R18
  4. Unfold `E = T + U`, `∂ₜ` → `fderiv`, derivative of the sum (first
     argument `by fun_prop`, second `hd`), evaluate, fold both back:         R19, R5, R20 (R6), R21, R5 backwards ×2
  5. Substitute the milestones:                                             rw [milestone 1, milestone 2]
  6. Merge the inner products, Newton, Hooke:                               R22, rw [h t], R23
  7. Close `⟪ẋ, -k • x + k • x⟫ = 0 t`:                                      R25 (R24)
-/
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

/- SKELETON · energy_const
  Prove the milestones first: 1 and 2 feed 3, and 3 is used in step 4.
  1. Zero derivative ⇒ constant; the side goal `Differentiable` is `by fun_prop`:   R26 (R6)
  2. `intro τ`; an equation of linear maps `Time →L[ℝ] ℝ` → their values at `p`:  R27
  3. Write `p = p.val • 1` and pull the scalar out; fold into `∂ₜ`:                 R28, R29, R5 backwards
  4. Substitute milestone 3:                                                      rw [milestone 3]
  5. Close `p.val • 0 τ = 0 (p.val • 1)`:                                          simp (R24, R30, R31)
-/
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
    `m ẍ = -k x`, so `dE/dt = 0`. A function `Time → ℝ` with zero derivative everywhere is constant; its
    derivative at `τ` is a linear map on `Time`, zero as soon as it sends `1` to `0`.
H2. Each energy derivative: `funext t`, a `hd : DifferentiableAt …` fact, unfold the energy (for `U` with
    `simp only [potentialEnergy_eq, smul_eq_mul, ← mul_assoc]`), then
    `rw [Time.deriv_eq, fderiv_const_mul (by fun_prop), _root_.smul_apply, fderiv_inner_apply ℝ hd hd, ← Time.deriv_eq]`,
    and collect the two equal inner products with `inner_smul_right`, `real_inner_comm` and `ring`.
    Sum: `energy_eq`, `fderiv_fun_add`, `_root_.add_apply`, the two milestones, `← inner_add_right`, Newton, `force_eq_linear`.
H3. Constancy: `apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (by fun_prop)`, `intro τ; ext p`, then
    `rw [p.eq_one_smul, map_smul, ← Time.deriv_eq, energy_deriv_zero S x hx h]; simp`.
    Kinetic part: `hd : DifferentiableAt ℝ (∂ₜ x) t := (Time.deriv_differentiable_of_contDiff x hx).differentiableAt`;
    potential part: `hd : DifferentiableAt ℝ x t := (hx.differentiable (by simp)).differentiableAt`.
-/

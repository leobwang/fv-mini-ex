/- H112 | Uniqueness of oscillator trajectories | 1-1.5 h | linearity of the EOM, energy method, Time.deriv, physlib
GOAL
  A smooth solution `x` of the harmonic oscillator's equation of motion with initial position `IC.x₀` and initial
  velocity `IC.v₀` is physlib's explicit trajectory `IC.trajectory S`. Use the energy method on `y = x − trajectory`.
BANNED: InitialConditions.trajectories_unique, ClassicalMechanics.DampedHarmonicOscillator.trajectories_unique, exact?, apply?, try?, hint
BANNED: ClassicalMechanics.DampedHarmonicOscillator.equationOfMotion_unique, ClassicalMechanics.DampedHarmonicOscillator.toUndamped_equationOfMotion

GUIDE
  Entries R1–R33: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time ContDiff InnerProductSpace

namespace H112

/- SKELETON · deriv_sub   (milestone 1; used in `eom_sub`, step 4, and `trajectory_unique`, step 3)
  1. Equality of functions → equality at a point `t`:                     R1
  2. Every `∂ₜ` → `fderiv ℝ _ t` applied to `1`:                           R2
  3. Split the derivative of the difference, with `hf t`, `hg t`:         R3
  4. Apply the difference of linear maps to `1`; the goal closes:         R4
     (2–4 fit in one `simp only [...]`)
-/
-- MILESTONE (optional: change or delete)
/-- `∂ₜ` of a difference of differentiable paths. -/
theorem deriv_sub (f g : Time → EuclideanSpace ℝ (Fin 1)) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) : ∂ₜ (fun t => f t - g t) = fun t => ∂ₜ f t - ∂ₜ g t := by
  sorry

/- SKELETON · eom_sub   (milestone 2; uses milestone 1; used in `trajectory_unique`, step 3)
  1. hT : ContDiff ℝ ∞ (IC.trajectory S)                                   R5
  2. hT2 : Newton's law for the trajectory                                 R9, then R10 with hT
  3. Newton's law for `x` in `h`, and as the goal for the difference
     (its smoothness is `hx.sub hT`); then `intro t`:                      R11, R12 with R6
  4. Split `∂ₜ (∂ₜ (x − T))` with milestone 1, twice, each `rw [deriv_sub _ _ h₁ h₂]`
     (with `_` for h₁ h₂, they become side goals after the main goal):
       inner ∂ₜ: h₁ h₂ = differentiability of x, T                       R7
       outer ∂ₜ: h₁ h₂ = differentiability of ∂ₜ x, ∂ₜ T                 R8
  5. Distribute `S.m •`, then substitute both Newton laws:                R13, rw [h, hT2]
  6. Hooke's law and distribute `-S.k •`; the goal closes:                R14, R13
-/
-- MILESTONE (optional: change or delete)
/-- The equation of motion is linear: the difference of two solutions is a solution. -/
theorem eom_sub (S : HarmonicOscillator) (IC : InitialConditions)
    (x : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x) :
    S.EquationOfMotion (fun t => x t - IC.trajectory S t) := by
  sorry

/- SKELETON · eq_zero_of_energy_zero   (milestone 3; used in `trajectory_unique`, step 4)
  1. Equality of functions → at a point `t` (goal `y t = 0 t`):           R1
  2. Both energy terms are nonnegative (as terms; the definitions unfold):
       hk : 0 ≤ S.kineticEnergy y t                 R16, R16 (`0 ≤ 1/2` by norm_num), R17, R18
       hp : 0 ≤ S.potentialEnergy (y t)             R19, R19, R17 (for S.k), R18
  3. h : S.potentialEnergy (y t) = 0, from `hE t`:                         R20
  4. In `h`: unfold `potentialEnergy`, `•` → `*`, product = 0 → a factor,
     `S.k = 0` → False (one `simp only [...] at h`):                       R15, R21, R22, R23
  5. Numerals and `⟪y t, y t⟫_ℝ = 0` → `y t = 0`:                           R25 (uses R24)
  6. Close the goal from `h`:                                              R26
-/
-- MILESTONE (optional: change or delete)
/-- A path whose energy vanishes at all times is identically zero. -/
theorem eq_zero_of_energy_zero (S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hE : ∀ t, S.energy y t = 0) : y = 0 := by
  sorry

/- SKELETON · trajectory_unique   (prove milestones 1 `deriv_sub`, 2 `eom_sub`, 3 `eq_zero_of_energy_zero` first)
  1. hT : ContDiff ℝ ∞ (IC.trajectory S)                                   R5
  2. Name the difference: y := fun t => x t - IC.trajectory S t, with hy   R27
  3. hE : ∀ t, S.energy y t = 0.  After `intro t`:
       energy at t → energy at 0 (smoothness `hx.sub hT`, EOM milestone 2)  R28, R6
       hv0 : ∂ₜ y 0 = 0   rw [hy, milestone 1 (args by R7)], then `simp [hv]`   R30
       hy0 : y 0 = 0      rw [hy], then `simp [h0]`                         R29
       unfold the energy, rw [hv0, hy0], close                             R15, R31
  4. `funext t`; milestone 3 on hE, evaluated at t; then `a - b = 0 → a = b`:   R1, R32, R33
-/
-- BEGIN SPEC
theorem trajectory_unique (S : HarmonicOscillator) (IC : InitialConditions)
    (x : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x)
    (h0 : x 0 = IC.x₀) (hv : ∂ₜ x 0 = IC.v₀) :
    x = IC.trajectory S :=
-- END SPEC
  sorry

end H112

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Set `y := fun t => x t - IC.trajectory S t`. It solves the EOM (linearity, milestone 2) and starts at rest at the
    origin, so its energy is `0` at time `0`; conservation makes it `0` forever, and zero energy forces `y = 0`
    (milestone 3). Milestone 1 (`∂ₜ` of a difference) is the tool for both the velocity and the acceleration of `y`.
H2. Milestone 2 goes through Newton's law: rewrite every EOM with `equationOfMotion_iff_newtons_2nd_law` (R10–R12),
    split `∂ₜ (∂ₜ y)` with `deriv_sub` twice (R7 then R8 for the differentiability arguments), then `smul_sub` and
    `force_eq_linear`. Milestone 3: both energy terms are `≥ 0` (`mul_nonneg`, `smul_nonneg`, `real_inner_self_nonneg`),
    so the potential term is `0` (`add_eq_zero_iff_of_nonneg`), and `S.k ≠ 0` leaves `⟪y t, y t⟫_ℝ = 0`.
H3. `deriv_sub`: `funext t; simp only [Time.deriv_eq, fderiv_fun_sub (hf t) (hg t), sub_apply]`.
    Main: `rw [S.energy_conservation_of_equationOfMotion' y (hx.sub hT) (eom_sub S IC x hx h)]`, then
    `simp [energy, kineticEnergy, potentialEnergy, hv0, hy0]` with `hv0 : ∂ₜ y 0 = 0`, `hy0 : y 0 = 0`; finish with
    `sub_eq_zero.mp (congrFun (eq_zero_of_energy_zero S y hE) t)`.
-/

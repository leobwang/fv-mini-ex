/- Guide for M185 (Energy of the oscillator trajectory).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a general `c • x + d • y`,
a general angle `θ`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time Real InnerProductSpace

namespace M185Guide

/-! # Part R · Reference entries -/

/-! ## The oscillator's constants -/

/-! ### R1. `HarmonicOscillator.ω_sq` · `S.ω ^ 2 = S.k / S.m` · goal
`S.ω` is defined as `√(S.k / S.m)`; this lemma squares the root away. -/
example (S : HarmonicOscillator) (P : ℝ → Prop) (h : P (S.k / S.m)) : P (S.ω ^ 2) := by
  rw [ω_sq]
  exact h

/-! ### R2. `field_simp [S.m_ne_zero]` · goal: clears `/ S.m`, closes the goal when a ring identity is left
`S.m_ne_zero : S.m ≠ 0` (and `S.ω_ne_zero : S.ω ≠ 0`, `S.k_ne_zero`) are physlib facts `field_simp` needs. -/
example (S : HarmonicOscillator) (a : ℝ) : a = S.m * (a / S.m) := by
  field_simp [S.m_ne_zero]

/-! ## Unfolding the energy and the trajectory -/

/-! ### R3. `simp only [energy, kineticEnergy, potentialEnergy]` · goal: `S.energy x τ` → its formula
`∂ₜ x τ` is the time derivative of `x : Time → EuclideanSpace ℝ (Fin 1)` at `τ`. -/
example (S : HarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1)) (τ : Time) (P : ℝ → Prop)
    (h : P (1 / 2 * S.m * ⟪∂ₜ x τ, ∂ₜ x τ⟫_ℝ + (1 / 2 : ℝ) • S.k • ⟪x τ, x τ⟫_ℝ)) :
    P (S.energy x τ) := by
  simp only [energy, kineticEnergy, potentialEnergy]
  exact h

/-! ### R4. `InitialConditions.trajectory_velocity` · goal: `∂ₜ (IC.trajectory S)` → explicit velocity
The lemma rewrites the function `∂ₜ (IC.trajectory S)`, so the result is a `fun t => …` applied to `τ`. -/
example (S : HarmonicOscillator) (IC : InitialConditions) (τ : Time) (P : EuclideanSpace ℝ (Fin 1) → Prop)
    (h : P (-S.ω • sin (S.ω * τ.val) • IC.x₀ + cos (S.ω * τ.val) • IC.v₀)) :
    P (∂ₜ (IC.trajectory S) τ) := by
  rw [InitialConditions.trajectory_velocity]
  exact h

/-! ### R5. `InitialConditions.trajectory_eq` · goal: `IC.trajectory S τ` → `cos (ωτ) • x₀ + (sin (ωτ)/ω) • v₀`
Used with `simp only`, which also performs the `(fun t => …) τ` application. -/
example (S : HarmonicOscillator) (IC : InitialConditions) (τ : Time) (P : EuclideanSpace ℝ (Fin 1) → Prop)
    (h : P (cos (S.ω * τ.val) • IC.x₀ + (sin (S.ω * τ.val) / S.ω) • IC.v₀)) :
    P (IC.trajectory S τ) := by
  simp only [InitialConditions.trajectory_eq]
  exact h

/-! ## Expanding inner products (`E` is any real inner product space, e.g. `EuclideanSpace ℝ (Fin 1)`) -/

/-! ### R6. `inner_add_left` · `⟪x + y, z⟫_ℝ = ⟪x, z⟫_ℝ + ⟪y, z⟫_ℝ` · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y z : E) (P : ℝ → Prop)
    (h : P (⟪x, z⟫_ℝ + ⟪y, z⟫_ℝ)) : P ⟪x + y, z⟫_ℝ := by
  rw [inner_add_left]
  exact h

/-! ### R7. `inner_add_right` · `⟪x, y + z⟫_ℝ = ⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ` · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y z : E) (P : ℝ → Prop)
    (h : P (⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ)) : P ⟪x, y + z⟫_ℝ := by
  rw [inner_add_right]
  exact h

/-! ### R8. `real_inner_smul_left` · `⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ` · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r : ℝ) (x y : E) (P : ℝ → Prop)
    (h : P (r * ⟪x, y⟫_ℝ)) : P ⟪r • x, y⟫_ℝ := by
  rw [real_inner_smul_left]
  exact h

/-! ### R9. `real_inner_smul_right` · `⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ` · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r : ℝ) (x y : E) (P : ℝ → Prop)
    (h : P (r * ⟪x, y⟫_ℝ)) : P ⟪x, r • y⟫_ℝ := by
  rw [real_inner_smul_right]
  exact h

/-! ### R10. `smul_eq_mul` · `a • b = a * b` when both are numbers · goal
The potential energy is written `(1 / 2) • S.k • ⟪x, x⟫_ℝ`: a scalar action of `ℝ` on `ℝ`. -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R11. `real_inner_comm x y` · `⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ` · goal: one cross term in a fixed order
Give both arguments: then it rewrites only `⟪y, x⟫_ℝ`, and the two cross terms become the same atom. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) (P : ℝ → Prop)
    (h : P ⟪x, y⟫_ℝ) : P ⟪y, x⟫_ℝ := by
  rw [real_inner_comm x y]
  exact h

/-! ### R12. `real_inner_self_eq_norm_sq` · `⟪x, x⟫_ℝ = ‖x‖ ^ 2` · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) (P : ℝ → Prop)
    (h : P (‖x‖ ^ 2)) : P ⟪x, x⟫_ℝ := by
  rw [real_inner_self_eq_norm_sq]
  exact h

/-! ## Finishing the real-number identity -/

/-! ### R13. `field_simp [S.ω_ne_zero]` · goal: multiplies out every `/ S.ω`
Both sides of the equation are multiplied by the denominators, then normalised. -/
example (S : HarmonicOscillator) (a b c : ℝ) (h : a * b + S.ω * c = S.ω * c) :
    a / S.ω * b + c = c := by
  field_simp [S.ω_ne_zero]
  exact h

/-! ### R14. `Real.sin_sq_add_cos_sq` · `sin θ ^ 2 + cos θ ^ 2 = 1` · goal -/
example (θ : ℝ) (P : ℝ → Prop) (h : P 1) : P (sin θ ^ 2 + cos θ ^ 2) := by
  rw [Real.sin_sq_add_cos_sq]
  exact h

/-! ### R15. `linear_combination e * h` · closes `a = b` when `a - b - e * (lhs h - rhs h)` is `0` by `ring`
Use it when the goal is an identity only modulo a fact `h` (here `sin² + cos² = 1`). -/
example (a θ : ℝ) : a * sin θ ^ 2 + a * cos θ ^ 2 = a := by
  linear_combination a * Real.sin_sq_add_cos_sq θ

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Potential energy of a general combination `c • x + d • y`: R3, R6–R11, R12, then `ring` -/
example (S : HarmonicOscillator) (c d : ℝ) (x y : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy (c • x + d • y) =
      1 / 2 * S.k * (c ^ 2 * ‖x‖ ^ 2 + 2 * c * d * ⟪x, y⟫_ℝ + d ^ 2 * ‖y‖ ^ 2) := by
  simp only [potentialEnergy]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, smul_eq_mul,
    real_inner_comm x y]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-! ### W2. Clear `/ S.ω`, then close modulo `sin² + cos² = 1`: R13, then R15 with R14 -/
example (S : HarmonicOscillator) (a θ : ℝ) :
    S.ω ^ 2 * a * (sin θ / S.ω) ^ 2 + a * cos θ ^ 2 = a := by
  field_simp [S.ω_ne_zero]
  linear_combination a * Real.sin_sq_add_cos_sq θ

end M185Guide

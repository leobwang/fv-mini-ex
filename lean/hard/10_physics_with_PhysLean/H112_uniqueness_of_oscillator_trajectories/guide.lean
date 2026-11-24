/- Guide for H112 (Uniqueness of oscillator trajectories).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact (`hx.sub hy`, `S.m_pos.le`, `(…).1 h`) use `have h := …`, so the context
gains `h` and you can read off exactly what was produced.
Part W: worked combinations on functions and equations that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time ContDiff InnerProductSpace

namespace H112Guide

/-! # Part R · Reference entries -/

/-! ## Derivatives in time: `∂ₜ`, `fderiv` -/

/-! ### R1. `funext t` · goal `f = g` (functions) → `f t = g t`; context gains `t` -/
example {α β : Type} (f g : α → β) (h : ∀ t, f t = g t) : f = g := by
  funext t
  exact h t

/-! ### R2. `Time.deriv_eq` · `∂ₜ f t = (fderiv ℝ f t) 1` · goal: `∂ₜ` → the Fréchet derivative at `1`
`fderiv ℝ f t : Time →L[ℝ] M` is the derivative of `f` at `t`, a continuous linear map; applying it
to the time step `1` gives the velocity. Use it with `simp only` (it rewrites every `∂ₜ`). -/
example {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (t : Time)
    (P : M → Prop) (h : P ((fderiv ℝ f t) 1)) : P (∂ₜ f t) := by
  simp only [Time.deriv_eq]
  exact h

/-! ### R3. `fderiv_fun_sub hf hg` · `fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x`
Needs `hf : DifferentiableAt ℝ f x`. From `hf : Differentiable ℝ f` (differentiable everywhere,
i.e. `∀ x, DifferentiableAt ℝ f x`) write `hf x`. -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f g : E → F) (x : E) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (P : (E →L[ℝ] F) → Prop)
    (h : P (fderiv ℝ f x - fderiv ℝ g x)) : P (fderiv ℝ (fun y => f y - g y) x) := by
  rw [fderiv_fun_sub hf hg]
  exact h

/-! ### R4. `sub_apply` · `(L - M) v = L v - M v` · goal: a difference of maps applied to a vector -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L M : E →L[ℝ] F) (v : E) (P : F → Prop) (h : P (L v - M v)) :
    P ((L - M) v) := by
  simp only [sub_apply]
  exact h

/-! ## Smoothness and differentiability facts -/

/-! ### R5. `fun_prop` · closes `ContDiff ℝ n f` (and `Differentiable ℝ f`, `Continuous f`) for `f` built
from smooth pieces. physlib tags `InitialConditions.trajectory_contDiff` for it, so it also proves
`ContDiff ℝ ∞ (IC.trajectory S)`. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (hf : ContDiff ℝ ∞ f)
    (c : ℝ) : ContDiff ℝ ∞ (fun t => c • f t) := by
  fun_prop

/-! ### R6. `ContDiff.sub` · `ContDiff 𝕜 n f → ContDiff 𝕜 n g → ContDiff 𝕜 n (fun x => f x - g x)`
· context gains the smoothness of the difference (write `hf.sub hg`). -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Time → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun t => f t - g t) := by
  have h := hf.sub hg
  exact h

/-! ### R7. `ContDiff.differentiable` · `ContDiff 𝕜 n f → n ≠ 0 → Differentiable 𝕜 f`
`hf.differentiable` alone still asks for `∞ ≠ 0`; `(by simp)` proves it on the spot. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Time → E)
    (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  have h := hf.differentiable (by simp)
  exact h

/-! ### R8. `Time.deriv_differentiable_of_contDiff` · `ContDiff ℝ ∞ f → Differentiable ℝ (∂ₜ f)`
· context gains: the velocity of a smooth path is differentiable (needed to split `∂ₜ (∂ₜ …)`). -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Time → E)
    (hf : ContDiff ℝ ∞ f) : Differentiable ℝ (∂ₜ f) := by
  have h := Time.deriv_differentiable_of_contDiff f hf
  exact h

/-! ## The equation of motion -/

/-! ### R9. `InitialConditions.trajectory_equationOfMotion` · context gains: the explicit trajectory
solves the equation of motion, `S.EquationOfMotion (IC.trajectory S)` (write `IC.trajectory_equationOfMotion S`). -/
example (IC : InitialConditions) (S : HarmonicOscillator) :
    S.EquationOfMotion (IC.trajectory S) := by
  have h := IC.trajectory_equationOfMotion S
  exact h

/-! ### R10. `(S.equationOfMotion_iff_newtons_2nd_law z hz).1 hE` · a proof of Newton's law for `z`
Use it as `have hz2 := …` (context gains it) or `exact …` (closes it, as here).
The lemma: `ContDiff ℝ ∞ z → (S.EquationOfMotion z ↔ ∀ t, S.m • ∂ₜ (∂ₜ z) t = S.force (z t))`.
`.1` (= `.mp`) is the `→` half of the `↔`. -/
example (S : HarmonicOscillator) (z : Time → EuclideanSpace ℝ (Fin 1)) (hz : ContDiff ℝ ∞ z)
    (hE : S.EquationOfMotion z) : ∀ t, S.m • ∂ₜ (∂ₜ z) t = S.force (z t) := by
  exact (S.equationOfMotion_iff_newtons_2nd_law z hz).1 hE

/-! ### R11. `rw [S.equationOfMotion_iff_newtons_2nd_law _ hz] at hE` · context: `hE` becomes Newton's law
The `_` is `z`; Lean reads it off `hz`. -/
example (S : HarmonicOscillator) (z : Time → EuclideanSpace ℝ (Fin 1)) (hz : ContDiff ℝ ∞ z)
    (hE : S.EquationOfMotion z) (G : Prop) (k : (∀ t, S.m • ∂ₜ (∂ₜ z) t = S.force (z t)) → G) :
    G := by
  rw [S.equationOfMotion_iff_newtons_2nd_law _ hz] at hE
  exact k hE

/-! ### R12. `rw [S.equationOfMotion_iff_newtons_2nd_law _ hz]` · goal: `S.EquationOfMotion z` → Newton's law -/
example (S : HarmonicOscillator) (z : Time → EuclideanSpace ℝ (Fin 1)) (hz : ContDiff ℝ ∞ z)
    (h : ∀ t, S.m • ∂ₜ (∂ₜ z) t = S.force (z t)) : S.EquationOfMotion z := by
  rw [S.equationOfMotion_iff_newtons_2nd_law _ hz]
  exact h

/-! ### R13. `smul_sub` · `r • (x - y) = r • x - r • y` · goal: distribute a scalar over `-` -/
example {E : Type} [AddCommGroup E] [Module ℝ E] (r : ℝ) (x y : E) (P : E → Prop)
    (h : P (r • x - r • y)) : P (r • (x - y)) := by
  rw [smul_sub]
  exact h

/-! ### R14. `HarmonicOscillator.force_eq_linear` · `S.force x = -S.k • x` · goal: Hooke's law -/
example (S : HarmonicOscillator) (x : EuclideanSpace ℝ (Fin 1))
    (P : EuclideanSpace ℝ (Fin 1) → Prop) (h : P (-S.k • x)) : P (S.force x) := by
  simp only [force_eq_linear]
  exact h

/-! ## Energy and positivity -/

/-! ### R15. `simp only [energy, kineticEnergy, potentialEnergy]` · goal: unfold the energy
`S.energy z t = 1 / 2 * S.m * ⟪∂ₜ z t, ∂ₜ z t⟫_ℝ + (1 / 2) • S.k • ⟪z t, z t⟫_ℝ`.
The scalar `(1 / 2)` in front of `•` is a REAL number; when you write it yourself, say `(1 / 2 : ℝ)`. -/
example (S : HarmonicOscillator) (z : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) (P : ℝ → Prop)
    (h : P (1 / 2 * S.m * ⟪∂ₜ z t, ∂ₜ z t⟫_ℝ + (1 / 2 : ℝ) • S.k • ⟪z t, z t⟫_ℝ)) :
    P (S.energy z t) := by
  simp only [energy, kineticEnergy, potentialEnergy]
  exact h

/-! ### R16. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · closes a sign goal from the two factors -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  exact mul_nonneg ha hb

/-! ### R17. `S.m_pos.le` (`S.m_pos : 0 < S.m`, then `LT.lt.le`) · context gains `0 ≤ S.m`
Same for `S.k_pos.le : 0 ≤ S.k`. -/
example (S : HarmonicOscillator) : 0 ≤ S.m := by
  have h := S.m_pos.le
  exact h

/-! ### R18. `real_inner_self_nonneg` · `0 ≤ ⟪x, x⟫_ℝ` · closes it; `x` is implicit, read off the goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) : 0 ≤ ⟪x, x⟫_ℝ := by
  exact real_inner_self_nonneg

/-! ### R19. `smul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a • b` · as R16, for `•` (here `ℝ` acting on `ℝ`) -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a • b := by
  exact smul_nonneg ha hb

/-! ### R20. `add_eq_zero_iff_of_nonneg` · `0 ≤ a → 0 ≤ b → (a + b = 0 ↔ a = 0 ∧ b = 0)`
`((add_eq_zero_iff_of_nonneg ha hb).mp hab).2` · context gains `b = 0`. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 0) : b = 0 := by
  have h := ((add_eq_zero_iff_of_nonneg ha hb).mp hab).2
  exact h

/-! ## From zero potential energy to zero position -/

/-! ### R21. `simp only [smul_eq_mul] at h` · context: `a • b` (both real) → `a * b` -/
example (a b c : ℝ) (G : Prop) (h : a • b • c = 0) (k : a * (b * c) = 0 → G) : G := by
  simp only [smul_eq_mul] at h
  exact k h

/-! ### R22. `simp only [mul_eq_zero] at h` · context: `a * b = 0` → `a = 0 ∨ b = 0` (nested to the right) -/
example (a b c : ℝ) (G : Prop) (h : a * (b * c) = 0) (k : a = 0 ∨ b = 0 ∨ c = 0 → G) : G := by
  simp only [mul_eq_zero] at h
  exact k h

/-! ### R23. `simp only [S.k_ne_zero] at h` · context: `S.k = 0` → `False`
`S.k_ne_zero : S.k ≠ 0`; given to `simp`, a hypothesis `a ≠ 0` rewrites `a = 0` to `False`. -/
example (S : HarmonicOscillator) (c : ℝ) (G : Prop) (h : S.k = 0 ∨ c = 0)
    (k : False ∨ c = 0 → G) : G := by
  simp only [S.k_ne_zero] at h
  exact k h

/-! ### R24. `inner_self_eq_zero` · `⟪x, x⟫_ℝ = 0 ↔ x = 0` · goal (or `at h`); a `simp` lemma, so `simp`, `norm_num` use it -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E)
    (h : x = 0) : ⟪x, x⟫_ℝ = 0 := by
  rw [inner_self_eq_zero]
  exact h

/-! ### R25. `norm_num` (or `norm_num at h`) · goal (or `h`): numeral facts decided (`1 / 2 = 0` → `False`),
`False ∨ A` → `A`, plus every `simp` lemma (so R24 too). In the exercise it runs `at h`. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) (h : x = 0) :
    (1 : ℝ) / 2 = 0 ∨ False ∨ ⟪x, x⟫_ℝ = 0 := by
  norm_num
  exact h

/-! ### R26. `simpa using h` · closes the goal when `simp` brings goal and `h` to the same form
`0 t` is the zero function applied to `t`; `simp` turns it into `0` (`Pi.zero_apply`). -/
example {α E : Type} [AddCommGroup E] (f : α → E) (t : α) (h : f t = 0) : f t = (0 : α → E) t := by
  simpa using h

/-! ## Naming the difference and using conservation -/

/-! ### R27. `set y := e with hy` · context gains `y := e` and `hy : y = e`; every `e` in the goal
becomes `y`. `rw [hy]` puts `e` back. -/
example (f g : ℝ → ℝ) (P : (ℝ → ℝ) → Prop) (h : P (fun t => f t - g t)) :
    P (fun t => f t - g t) := by
  set y := fun t => f t - g t with hy
  exact h

/-! ### R28. `HarmonicOscillator.energy_conservation_of_equationOfMotion'` · goal: energy at `t` → at `0`
`S.energy_conservation_of_equationOfMotion' z hz hE t : S.energy z t = S.energy z 0`, for
`hz : ContDiff ℝ ∞ z`, `hE : S.EquationOfMotion z`. Under `rw`, leave `t` out: Lean finds it. -/
example (S : HarmonicOscillator) (z : Time → EuclideanSpace ℝ (Fin 1)) (hz : ContDiff ℝ ∞ z)
    (hE : S.EquationOfMotion z) (t : Time) (P : ℝ → Prop) (h : P (S.energy z 0)) :
    P (S.energy z t) := by
  rw [S.energy_conservation_of_equationOfMotion' z hz hE]
  exact h

/-! ### R29. `InitialConditions.trajectory_position_at_zero` · `IC.trajectory S 0 = IC.x₀` · goal (a `simp` lemma) -/
example (IC : InitialConditions) (S : HarmonicOscillator) (P : EuclideanSpace ℝ (Fin 1) → Prop)
    (h : P IC.x₀) : P (IC.trajectory S 0) := by
  rw [InitialConditions.trajectory_position_at_zero]
  exact h

/-! ### R30. `InitialConditions.trajectory_velocity_at_zero` · `∂ₜ (IC.trajectory S) 0 = IC.v₀` · goal (a `simp` lemma) -/
example (IC : InitialConditions) (S : HarmonicOscillator) (P : EuclideanSpace ℝ (Fin 1) → Prop)
    (h : P IC.v₀) : P (∂ₜ (IC.trajectory S) 0) := by
  rw [InitialConditions.trajectory_velocity_at_zero]
  exact h

/-! ### R31. `simp` on `⟪0, 0⟫_ℝ` · closes it: `inner_zero_left`, `mul_zero`, `smul_zero`, `add_zero` -/
example (a b : ℝ) : a * ⟪(0 : EuclideanSpace ℝ (Fin 1)), 0⟫_ℝ + b • ⟪(0 : EuclideanSpace ℝ (Fin 1)), 0⟫_ℝ = 0 := by
  simp

/-! ## From `y = 0` back to `x = trajectory` -/

/-! ### R32. `congrFun h t` · `f = g → f t = g t` · context gains the equation at one point -/
example {α β : Type} (f g : α → β) (hfg : f = g) (t : α) : f t = g t := by
  have h := congrFun hfg t
  exact h

/-! ### R33. `sub_eq_zero` · `a - b = 0 ↔ a = b`; `sub_eq_zero.mp` closes `a = b` from `a - b = 0` -/
example {E : Type} [AddCommGroup E] (a b : E) (hab : a - b = 0) : a = b := by
  exact sub_eq_zero.mp hab

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. `∂ₜ` of a SUM, the same way as a difference: R1, R2, then `fderiv_fun_add`, `add_apply` -/
example {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (f g : Time → M)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    ∂ₜ (fun t => f t + g t) = fun t => ∂ₜ f t + ∂ₜ g t := by
  funext t
  simp only [Time.deriv_eq]
  rw [fderiv_fun_add (hf t) (hg t)]
  simp only [add_apply]

/-! ### W2. Zero weighted square ⇒ zero vector: R21, R22, R23-style `simp`, then R25 -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ℝ) (hc : c ≠ 0) (v : E)
    (h : (1 / 3 : ℝ) • c • ⟪v, v⟫_ℝ = 0) : v = 0 := by
  simp only [smul_eq_mul, mul_eq_zero, hc] at h
  norm_num at h
  exact h

/-! ### W3. A difference that vanishes as a function: R1, R32, R33 -/
example (f g : ℝ → ℝ) (h : (fun t => f t - g t) = 0) : f = g := by
  funext t
  have ht := congrFun h t
  simp only [Pi.zero_apply] at ht
  exact sub_eq_zero.mp ht

end H112Guide

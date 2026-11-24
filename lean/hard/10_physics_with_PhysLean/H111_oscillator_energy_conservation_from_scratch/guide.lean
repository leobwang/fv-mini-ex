/- Guide for H111 (Oscillator energy conservation from scratch).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact from a hypothesis (`hf.differentiableAt`, `S.potentialEnergy_differentiable …`)
use `have h := …`, so the context gains `h` and you can read off exactly what was produced.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

open ClassicalMechanics HarmonicOscillator Time ContDiff InnerProductSpace

namespace H111Guide

/-! # Part R · Reference entries -/

/-! ## Functions of time: `∂ₜ`, `fderiv`, differentiability -/

/-! ### R1. `funext t` · goal `F = fun t => G t` → context gains `t : Time`, goal `F t = G t` -/
example {β : Type} (F G : Time → β) (h : ∀ t, F t = G t) : F = fun t => G t := by
  funext t
  exact h t

/-! ### R2. `Time.deriv_differentiable_of_contDiff` · context gains `Differentiable ℝ (∂ₜ f)`
From `hf : ContDiff ℝ ∞ f` (f smooth): its time derivative is differentiable again. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F) (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (∂ₜ f) := by
  have h := Time.deriv_differentiable_of_contDiff f hf
  exact h

/-! ### R3. `Differentiable.differentiableAt` · context gains `DifferentiableAt ℝ f t`
`Differentiable ℝ f` is "differentiable at every point"; `hf.differentiableAt` picks the point.
State the point in the `have`, or Lean cannot guess it. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F)
    (hf : Differentiable ℝ f) (t : Time) : DifferentiableAt ℝ f t := by
  have h : DifferentiableAt ℝ f t := hf.differentiableAt
  exact h

/-! ### R4. `kineticEnergy_eq` · goal: `S.kineticEnergy x` → `fun t => 1 / 2 * S.m * ⟪∂ₜ x t, ∂ₜ x t⟫_ℝ` -/
example (S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1))
    (P : (Time → ℝ) → Prop) (h : P (fun t => 1 / 2 * S.m * ⟪∂ₜ y t, ∂ₜ y t⟫_ℝ)) :
    P (S.kineticEnergy y) := by
  rw [kineticEnergy_eq]
  exact h

/-! ### R5. `Time.deriv_eq` · goal: `∂ₜ f t` → `fderiv ℝ f t 1` (the derivative map applied to `1`)
`rw [← Time.deriv_eq]` folds `fderiv ℝ f t 1` back into `∂ₜ f t`. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F) (t : Time)
    (P : F → Prop) (h : P (fderiv ℝ f t 1)) : P (∂ₜ f t) := by
  rw [Time.deriv_eq]
  exact h

/-! ### R6. `fun_prop` · closes a `Differentiable` / `DifferentiableAt` goal built from known pieces
It combines `+`, `*`, `•`, `⟪·,·⟫_ℝ`, constants, hypotheses in the context and every lemma tagged
`@[fun_prop]` (physlib tags R2, R18 and the energy lemmas, so `hx : ContDiff ℝ ∞ x` is enough). -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : Time → E)
    (hf : Differentiable ℝ f) (c : ℝ) (t : Time) :
    DifferentiableAt ℝ (fun τ => c * ⟪f τ, f τ⟫_ℝ) t := by
  fun_prop

/-! ### R7. `fderiv_const_mul` · goal: `fderiv ℝ (fun y => b * a y) x` → `b • fderiv ℝ a x`
Takes `ha : DifferentiableAt ℝ a x` first: `rw [fderiv_const_mul ha]` or `(by fun_prop)`.
`*` groups to the left: `1 / 2 * m * g y` is `(1 / 2 * m) * g y`, so `b = 1 / 2 * m`. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → ℝ) (b : ℝ) (x : E)
    (ha : DifferentiableAt ℝ a x) (P : (E →L[ℝ] ℝ) → Prop) (h : P (b • fderiv ℝ a x)) :
    P (fderiv ℝ (fun y => b * a y) x) := by
  rw [fderiv_const_mul ha]
  exact h

/-! ### R8. `_root_.smul_apply` · goal: `(c • L) v` → `c • L v` (a scaled linear map, evaluated)
Write `_root_.` because `open Time` makes plain `smul_apply` mean another lemma. -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (c : ℝ) (v : E) (P : F → Prop) (h : P (c • L v)) :
    P ((c • L) v) := by
  rw [_root_.smul_apply]
  exact h

/-! ### R9. `fderiv_inner_apply ℝ hf hg` · goal: derivative of `⟪f y, g y⟫_ℝ` → product rule
`fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v = ⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ`.
The field `ℝ` is an explicit argument. -/
example {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (f g : G → E) (x v : G) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (P : ℝ → Prop)
    (h : P (⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ)) :
    P (fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v) := by
  rw [fderiv_inner_apply ℝ hf hg]
  exact h

/-! ## Inner products and real arithmetic -/

/-! ### R10. `inner_smul_right` · goal: `⟪u, r • w⟫_ℝ` → `r * ⟪u, w⟫_ℝ` -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u w : E) (r : ℝ)
    (P : ℝ → Prop) (h : P (r * ⟪u, w⟫_ℝ)) : P ⟪u, r • w⟫_ℝ := by
  rw [inner_smul_right]
  exact h

/-! ### R11. `real_inner_comm` · `real_inner_comm u w : ⟪w, u⟫_ℝ = ⟪u, w⟫_ℝ`
Give the first argument (`real_inner_comm u`) so only `⟪_, u⟫_ℝ` is swapped. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u w : E)
    (P : ℝ → Prop) (h : P ⟪u, w⟫_ℝ) : P ⟪w, u⟫_ℝ := by
  rw [real_inner_comm u]
  exact h

/-! ### R12. `ring` · closes a real identity; inner products are unknowns, `•` between reals is `*` -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u w : E) (m : ℝ) :
    (1 / 2 * m) • (⟪u, w⟫_ℝ + ⟪u, w⟫_ℝ) = m * ⟪u, w⟫_ℝ := by
  ring

/-! ### R13. `ContDiff.differentiable` · context gains `Differentiable ℝ f` from `ContDiff ℝ ∞ f`
Its argument is `n ≠ 0`; for `n = ∞` write `hf.differentiable (by simp)`. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Time → F) (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ f := by
  have h := hf.differentiable (by simp)
  exact h

/-! ### R14. `potentialEnergy_eq` · goal: `S.potentialEnergy y` → `(1 / 2) • S.k • ⟪y, y⟫_ℝ`
Use `simp only [potentialEnergy_eq]`: inside `fun t => …` `rw` cannot reach `y = x t`. -/
example (S : HarmonicOscillator) (y : EuclideanSpace ℝ (Fin 1)) (P : ℝ → Prop)
    (h : P ((1 / 2 : ℝ) • S.k • ⟪y, y⟫_ℝ)) : P (S.potentialEnergy y) := by
  simp only [potentialEnergy_eq]
  exact h

/-! ### R15. `smul_eq_mul` · goal: `a • b` → `a * b` when both are reals -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R16. `mul_assoc` · `a * b * c = a * (b * c)`; `← mul_assoc` regroups to the left -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * b * c)) : P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ## The oscillator: equation of motion, energy, force -/

/-! ### R17. `equationOfMotion_iff_newtons_2nd_law S y hy` · context: `h` becomes Newton's law
`rw [… ] at h` rewrites a hypothesis instead of the goal. -/
example (S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1)) (hy : ContDiff ℝ ∞ y)
    (h : S.EquationOfMotion y) : ∀ t, S.m • ∂ₜ (∂ₜ y) t = S.force (y t) := by
  rw [equationOfMotion_iff_newtons_2nd_law S y hy] at h
  exact h

/-! ### R18. `S.potentialEnergy_differentiable y hy` · context gains differentiability of `t ↦ U(y t)`
It is `Differentiable`; applied to a point `t` it gives `DifferentiableAt` (as in R3). -/
example (S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1)) (hy : ContDiff ℝ ∞ y)
    (t : Time) : DifferentiableAt ℝ (fun t => S.potentialEnergy (y t)) t := by
  have h := S.potentialEnergy_differentiable y hy t
  exact h

/-! ### R19. `energy_eq` · goal: `S.energy y` → `fun t => S.kineticEnergy y t + S.potentialEnergy (y t)` -/
example (S : HarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1)) (P : (Time → ℝ) → Prop)
    (h : P (fun t => S.kineticEnergy y t + S.potentialEnergy (y t))) : P (S.energy y) := by
  rw [energy_eq]
  exact h

/-! ### R20. `fderiv_fun_add hf hg` · goal: `fderiv ℝ (fun y => f y + g y) x` → `fderiv ℝ f x + fderiv ℝ g x` -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f g : E → F) (x : E) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (P : (E →L[ℝ] F) → Prop) (h : P (fderiv ℝ f x + fderiv ℝ g x)) :
    P (fderiv ℝ (fun y => f y + g y) x) := by
  rw [fderiv_fun_add hf hg]
  exact h

/-! ### R21. `_root_.add_apply` · goal: `(L + M) v` → `L v + M v` (a sum of linear maps, evaluated) -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L M : E →L[ℝ] F) (v : E) (P : F → Prop) (h : P (L v + M v)) :
    P ((L + M) v) := by
  rw [_root_.add_apply]
  exact h

/-! ### R22. `inner_add_right` · `⟪u, w + z⟫_ℝ = ⟪u, w⟫_ℝ + ⟪u, z⟫_ℝ`; `← …` merges two inner products -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u w z : E)
    (P : ℝ → Prop) (h : P ⟪u, w + z⟫_ℝ) : P (⟪u, w⟫_ℝ + ⟪u, z⟫_ℝ) := by
  rw [← inner_add_right]
  exact h

/-! ### R23. `force_eq_linear` · goal: `S.force y` → `-S.k • y` (Hooke's law) -/
example (S : HarmonicOscillator) (y : EuclideanSpace ℝ (Fin 1))
    (P : EuclideanSpace ℝ (Fin 1) → Prop) (h : P (-S.k • y)) : P (S.force y) := by
  rw [force_eq_linear]
  exact h

/-! ### R24. `Pi.zero_apply` · goal: `0 t` (the zero function applied to `t`) → `0` -/
example {β : Type} [Zero β] (t : Time) (P : β → Prop) (h : P 0) : P ((0 : Time → β) t) := by
  rw [Pi.zero_apply]
  exact h

/-! ### R25. `simp` · closes `⟪u, -c • w + c • w⟫_ℝ = 0`
It uses `neg_smul` (`-c • w = -(c • w)`), `neg_add_cancel` (`-a + a = 0`), `inner_zero_right`. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u w : E) (c : ℝ) :
    ⟪u, -c • w + c • w⟫_ℝ = 0 := by
  simp

/-! ## Zero derivative ⇒ constant -/

/-! ### R26. `is_const_of_fderiv_eq_zero` · goal `f x = f y` → `∀ z, fderiv ℝ f z = 0`
`apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) hf` with `hf : Differentiable ℝ f` (or `(by fun_prop)`).
`(𝕜 := ℝ)` names the field, which Lean cannot infer from the goal. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (hf : Differentiable ℝ f)
    (x y : E) (h : ∀ z, fderiv ℝ f z = 0) : f x = f y := by
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) hf
  exact h

/-! ### R27. `ext p` on `Time →L[ℝ] F` · goal `L = M` → context gains `p : Time`, goal `L p = M p` -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Time →L[ℝ] F)
    (h : ∀ p, L p = (0 : Time →L[ℝ] F) p) : L = 0 := by
  ext p
  exact h p

/-! ### R28. `Time.eq_one_smul` · `p = p.val • 1`; `rw [p.eq_one_smul]` replaces every `p` in the goal
`p.val : ℝ` is the number underlying `p : Time`, and `1 : Time` is one unit of time. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Time →L[ℝ] F) (p : Time)
    (P : F → Prop) (h : P (L (p.val • 1))) : P (L p) := by
  rw [p.eq_one_smul]
  exact h

/-! ### R29. `map_smul` · goal: `L (c • v)` → `c • L v` (linearity pulls the scalar out) -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Time →L[ℝ] F) (c : ℝ) (v : Time)
    (P : F → Prop) (h : P (c • L v)) : P (L (c • v)) := by
  rw [map_smul]
  exact h

/-! ### R30. `zero_apply` · goal: `0 v` (the zero linear map applied) → `0` -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (v : Time) (P : F → Prop) (h : P 0) :
    P ((0 : Time →L[ℝ] F) v) := by
  rw [zero_apply]
  exact h

/-! ### R31. `smul_zero` · goal: `c • 0` → `0` -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) (P : F → Prop) (h : P 0) :
    P (c • (0 : F)) := by
  rw [smul_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. The product rule in `∂ₜ` form: R5, R9, then R5 backwards twice -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f g : Time → E)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (t : Time) :
    ∂ₜ (fun τ => ⟪f τ, g τ⟫_ℝ) t = ⟪f t, ∂ₜ g t⟫_ℝ + ⟪∂ₜ f t, g t⟫_ℝ := by
  rw [Time.deriv_eq]
  rw [fderiv_inner_apply ℝ (hf t) (hg t)]
  rw [← Time.deriv_eq, ← Time.deriv_eq]

/-! ### W2. `d/dt (3 ⟪f, f⟫) = 6 ⟪f, ḟ⟫`: R5, R7 (R6), R8, R9, R5 backwards, R11, R12 -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : Time → E)
    (hf : Differentiable ℝ f) (t : Time) :
    ∂ₜ (fun τ => 3 * ⟪f τ, f τ⟫_ℝ) t = 6 * ⟪f t, ∂ₜ f t⟫_ℝ := by
  rw [Time.deriv_eq]
  rw [fderiv_const_mul (by fun_prop)]
  rw [_root_.smul_apply]
  rw [fderiv_inner_apply ℝ (hf t) (hf t)]
  rw [← Time.deriv_eq]
  rw [real_inner_comm (f t)]
  ring

/-! ### W3. A linear map on `Time` is fixed by its value at `1`: R27, R28, R29, then `simp` -/
example (L : Time →L[ℝ] ℝ) (h1 : L 1 = 0) : L = 0 := by
  ext p
  rw [p.eq_one_smul]
  rw [map_smul]
  rw [h1]
  simp

end H111Guide

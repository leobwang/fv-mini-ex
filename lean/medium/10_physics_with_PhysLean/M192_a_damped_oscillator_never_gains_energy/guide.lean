/- Guide for M192 (A damped oscillator never gains energy).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `k`) in an entry is only there to finish the example; it shows what the goal or the
context became.
Part W: worked combinations on objects that are NOT the exercise's (the map `Time → ℝ` instead of
`ℝ → Time`, two inner products instead of one).
Assumed: Lean basics.
-/
import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic

open ClassicalMechanics Time ContDiff InnerProductSpace

namespace M192Guide

/-! # Part R · Reference entries -/

/-! ## The energy is differentiable -/

/-! ### R1. `HarmonicOscillator.energy_differentiable` · context gains `Differentiable ℝ (S.energy y)`
`S.energy_differentiable y hy : Differentiable ℝ (S.energy y)` for a smooth path `y`
(`hy : ContDiff ℝ ∞ y`). `S : DampedHarmonicOscillator` extends `HarmonicOscillator`, so
`S.energy` and `S.energy_differentiable` are the undamped oscillator's, reached through `S`. -/
example (S : DampedHarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hy : ContDiff ℝ ∞ y) (P : Prop) (k : Differentiable ℝ (S.energy y) → P) : P := by
  have hE := S.energy_differentiable y hy
  exact k hE

/-! ## From `Time` to `ℝ` -/

/-! ### R2. `let g : ℝ → ℝ := f ∘ Time.toRealCLE.symm` · context gains `g` together with its body
`Time.toRealCLE : Time ≃L[ℝ] ℝ` is the continuous linear bijection `t ↦ t.val`; `.symm : ℝ ≃L[ℝ] Time`
is its inverse `r ↦ ⟨r⟩`. Precomposing turns a function on `Time` into a function on `ℝ`. -/
example (f : Time → ℝ) (P : (ℝ → ℝ) → Prop) (h : P (f ∘ Time.toRealCLE.symm)) :
    P (f ∘ Time.toRealCLE.symm) := by
  let g : ℝ → ℝ := f ∘ Time.toRealCLE.symm
  exact h

/-! ### R3. `Differentiable.comp` · `hv.comp hu : Differentiable ℝ (v ∘ u)` · context
Note the order: the outer function's proof comes first. -/
example {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (u : E → F) (v : F → G)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (P : Prop)
    (k : Differentiable ℝ (v ∘ u) → P) : P := by
  have h := hv.comp hu
  exact k h

/-! ### R4. `ContinuousLinearEquiv.differentiable`, `.differentiableAt` · context
A continuous linear equivalence `e` is differentiable everywhere: `e.differentiable`, and at one
point `e.differentiableAt`. `Time.toRealCLE.symm.differentiable` is the case the exercise needs. -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (P : Prop) (k : Differentiable ℝ e → P) : P := by
  have h := e.differentiable
  exact k h

example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (x : E) (P : Prop) (k : DifferentiableAt ℝ e x → P) :
    P := by
  have h := e.differentiableAt (x := x)
  exact k h

/-! ### R5. `hf t` · context: `Differentiable ℝ f` → `DifferentiableAt ℝ f t`
`Differentiable ℝ f` is by definition `∀ t, DifferentiableAt ℝ f t`, so apply it to a point; `hf _`
lets Lean find the point. -/
example (f : Time → ℝ) (hf : Differentiable ℝ f) (t : Time) (P : Prop)
    (k : DifferentiableAt ℝ f t → P) : P := by
  have h := hf t
  exact k h

/-! ## The chain rule, step by step -/

/-! ### R6. `fderiv_apply_one_eq_deriv` · `(fderiv 𝕜 u r) 1 = deriv u r`; used right to left · goal
`deriv u r` (one-variable derivative, printed `_root_.deriv` because `Time.deriv` is open) becomes the
Fréchet derivative `fderiv ℝ u r : ℝ →L[ℝ] F` applied to the direction `1`. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (u : ℝ → F) (r : ℝ) (P : F → Prop)
    (h : P (fderiv ℝ u r 1)) : P (deriv u r) := by
  rw [← fderiv_apply_one_eq_deriv]
  exact h

/-! ### R7. `fderiv_comp` · `fderiv 𝕜 (v ∘ u) x = fderiv 𝕜 v (u x) ∘SL fderiv 𝕜 u x` · goal
Arguments: the point `x` (or `_`), then `DifferentiableAt` of `v` at `u x` (R5), then of `u` at `x` (R4).
`∘SL` is composition of continuous linear maps (`A.comp B`). -/
example {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (u : E → F) (v : F → G) (x : E)
    (hv : DifferentiableAt ℝ v (u x)) (hu : DifferentiableAt ℝ u x)
    (P : (E →L[ℝ] G) → Prop) (h : P ((fderiv ℝ v (u x)).comp (fderiv ℝ u x))) :
    P (fderiv ℝ (v ∘ u) x) := by
  rw [fderiv_comp x hv hu]
  exact h

/-! ### R8. `ContinuousLinearEquiv.fderiv` · `fderiv 𝕜 (⇑e) x = ↑e` · goal
A linear map is its own derivative. `⇑e` is `e` used as a function, `↑e` is `e` as a continuous
linear map `E →L[ℝ] F`. -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (x : E) (P : (E →L[ℝ] F) → Prop) (h : P ↑e) :
    P (fderiv ℝ e x) := by
  rw [ContinuousLinearEquiv.fderiv]
  exact h

/-! ### R9. `Time.deriv_eq` · `∂ₜ f t = fderiv ℝ f t 1` · goal
physlib's time derivative `∂ₜ f t` (`Time.deriv`) IS the Fréchet derivative in the direction
`1 : Time`; this lemma (or `rfl`) unfolds it. -/
example {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (t : Time)
    (P : M → Prop) (h : P (fderiv ℝ f t 1)) : P (∂ₜ f t) := by
  rw [Time.deriv_eq]
  exact h

/-! ### R10. `ContinuousLinearMap.comp_apply` · `(A ∘SL B) w = A (B w)` · goal -/
example {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (A : F →L[ℝ] G) (B : E →L[ℝ] F)
    (w : E) (P : G → Prop) (h : P (A (B w))) : P ((A.comp B) w) := by
  rw [ContinuousLinearMap.comp_apply]
  exact h

/-! ## Matching the direction: `↑toRealCLE.symm 1 = 1` -/

/-! ### R11. `congr 1` · goal `A a = A b` → `a = b` (same function, compare the arguments)
`congr` closes the new goal itself when it is `rfl` or a hypothesis; here it is neither. -/
example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : ℝ →L[ℝ] F) (a b : ℝ)
    (h : b = a) : A a = A b := by
  congr 1
  exact h.symm

/-! ### R12. `ext` (lemma `Time.ext`) · goal `s = t` in `Time` → `s.val = t.val`
`Time` is a structure with one field `val : ℝ`, so two times are equal when their values are. -/
example (s t : Time) (h : s.val = t.val) : s = t := by
  ext
  exact h

/-! ### R13. `simp [Time.toRealCLE]` · goal: `(↑toRealCLE.symm r).val` → `r`
Unfolding `toRealCLE` lets `simp` see that `.symm` sends `r` to `⟨r⟩`, whose `val` is `r`. -/
example (r : ℝ) (P : ℝ → Prop) (h : P r) :
    P ((Time.toRealCLE.symm : ℝ →L[ℝ] Time) r).val := by
  simp [Time.toRealCLE]
  exact h

/-! ### R14. `Time.one_val` · `val 1 = 1` · goal: the value of the time `1` is the real `1` -/
example (P : ℝ → Prop) (h : P 1) : P (1 : Time).val := by
  rw [Time.one_val]
  exact h

/-! ## The sign of the derivative -/

/-! ### R15. `DampedHarmonicOscillator.energy_dissipation_rate` · goal
`S.energy_dissipation_rate y t hm hy : ∂ₜ (S.energy y) t = -S.γ * ⟪∂ₜ y t, ∂ₜ y t⟫_ℝ`, for `y`
solving the damped equation (`hm`) and smooth (`hy`). -/
example (S : DampedHarmonicOscillator) (y : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (hm : S.EquationOfMotion y) (hy : ContDiff ℝ ∞ y) (P : ℝ → Prop)
    (h : P (-S.γ * ⟪∂ₜ y t, ∂ₜ y t⟫_ℝ)) : P (∂ₜ (S.energy y) t) := by
  rw [S.energy_dissipation_rate y t hm hy]
  exact h

/-! ### R16. `DampedHarmonicOscillator.γ_nonneg` · context gains `0 ≤ S.γ` (a field of `S`) -/
example (S : DampedHarmonicOscillator) (P : Prop) (k : 0 ≤ S.γ → P) : P := by
  have h := S.γ_nonneg
  exact k h

/-! ### R17. `real_inner_self_nonneg` · context gains `0 ≤ ⟪v, v⟫_ℝ`
The vector is an implicit argument named `x`: write `real_inner_self_nonneg (x := v)`. -/
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (v : F) (P : Prop)
    (k : 0 ≤ ⟪v, v⟫_ℝ → P) : P := by
  have h := real_inner_self_nonneg (x := v)
  exact k h

/-! ### R18. `nlinarith` · closes a real inequality that needs a product of hypotheses
Here it multiplies `0 ≤ c` and `0 ≤ q`. Plain `linarith` cannot: `c * q` is not linear. -/
example (c q : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q) : -c * q ≤ 0 := by
  nlinarith

/-! ## Derivative ≤ 0 ⇒ the function decreases -/

/-! ### R19. `antitone_of_deriv_nonpos` · context gains `Antitone g`
`antitone_of_deriv_nonpos hg hg' : Antitone g` for `g : ℝ → ℝ` (only `ℝ → ℝ`) from
`hg : Differentiable ℝ g` and `hg' : ∀ r, deriv g r ≤ 0`. -/
example (g : ℝ → ℝ) (hg : Differentiable ℝ g) (hg' : ∀ r, deriv g r ≤ 0) (P : Prop)
    (k : Antitone g → P) : P := by
  have hA := antitone_of_deriv_nonpos hg hg'
  exact k hA

/-! ### R20. `Time.le_def` · `s ≤ t ↔ s.val ≤ t.val` · context: use `.mp` to get the real inequality -/
example (s t : Time) (hst : s ≤ t) (P : Prop) (k : s.val ≤ t.val → P) : P := by
  have h := (Time.le_def s t).mp hst
  exact k h

/-! ### R21. `hA hab` · `Antitone g` is `∀ ⦃a b⦄, a ≤ b → g b ≤ g a`: apply it to `hab : a ≤ b` -/
example (g : ℝ → ℝ) (hA : Antitone g) (a b : ℝ) (hab : a ≤ b) : g b ≤ g a := by
  exact hA hab

/-! ### R22. `exact` up to unfolding · `(f ∘ ⇑toRealCLE.symm) t.val` is `f t` by definition
`toRealCLE.symm t.val` unfolds to `⟨t.val⟩`, which is `t`, so `exact` accepts the `ℝ`-side fact
for the `Time`-side goal; no rewriting needed. -/
example (f : Time → ℝ) (t : Time) (P : ℝ → Prop) (h : P ((f ∘ Time.toRealCLE.symm) t.val)) :
    P (f t) := by
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The chain rule the other way, for `u ∘ toRealCLE : Time → ℝ`: R9, R7, R8, R10, R6, R11 -/
example (u : ℝ → ℝ) (hu : Differentiable ℝ u) (t : Time) :
    ∂ₜ (u ∘ Time.toRealCLE) t = deriv u t.val := by
  rw [Time.deriv_eq]
  rw [fderiv_comp t (hu _) Time.toRealCLE.differentiableAt]
  rw [ContinuousLinearEquiv.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [← fderiv_apply_one_eq_deriv]
  congr 1
  simp [Time.toRealCLE]

/-! ### W2. Signs from two inner products: R17 twice, then R18 -/
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (c : ℝ) (v w : F)
    (hc : 0 ≤ c) : -c * ⟪v, v⟫_ℝ - ⟪w, w⟫_ℝ ≤ 0 := by
  have hv := real_inner_self_nonneg (x := v)
  have hw := real_inner_self_nonneg (x := w)
  nlinarith

end M192Guide

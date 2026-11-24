/- Guide for M182 (The curl of a gradient vanishes).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is a goal the entry does not touch.
Part W: worked combinations on objects that are NOT the exercise's (a constant vector field, a
symmetric table `g : Fin 3 → Fin 3 → ℝ`, a C² function on an arbitrary normed space `E`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.SpaceAndTime.Space.Derivatives.Curl

open Space

namespace M182Guide

/-! # Part R · Reference entries -/

/-! ## Partial derivatives `∂[μ]` → Fréchet derivatives `fderiv` -/

/-! ### R1. `Space.deriv_eq_fderiv_fun` · goal: the FUNCTION `∂[μ] g` → `fun x => fderiv ℝ g x (basis μ)`
`∂[μ] g` is notation for `Space.deriv μ g` and prints that way. Use it for an inner `∂`, which is a
function, not a number. -/
example (μ ν : Fin 3) (g : Space → ℝ) (x : Space) (P : ℝ → Prop)
    (h : P (∂[ν] (fun x => (fderiv ℝ (fun x => g x) x) (basis μ)) x)) : P (∂[ν] (∂[μ] g) x) := by
  rw [deriv_eq_fderiv_fun μ g]
  exact h

/-! ### R2. `Space.deriv_eq` · goal: the NUMBER `∂[μ] g x` → `fderiv ℝ g x (basis μ)` -/
example (μ : Fin 3) (g : Space → ℝ) (x : Space) (P : ℝ → Prop)
    (h : P ((fderiv ℝ g x) (basis μ))) : P (∂[μ] g x) := by
  rw [Space.deriv_eq]
  exact h

/-! ## Differentiating an application `c y (u y)` -/

/-! ### R3. `fderiv_clm_apply` · goal: derivative of `fun y => c y (u y)` → a product rule
`DifferentiableAt c x → DifferentiableAt u x →
   fderiv ℝ (fun y => c y (u y)) x = c x ∘L fderiv ℝ u x + (fderiv ℝ c x).flip (u x)`.
Without the two arguments, `rw` adds them as side goals; `(by fun_prop)` (R4) closes them. -/
example {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (c : E → F →L[ℝ] G) (u : E → F)
    (x : E) (hc : DifferentiableAt ℝ c x) (hu : DifferentiableAt ℝ u x) (P : (E →L[ℝ] G) → Prop)
    (h : P (c x ∘L fderiv ℝ u x + (fderiv ℝ c x).flip (u x))) :
    P (fderiv ℝ (fun y => c y (u y)) x) := by
  rw [fderiv_clm_apply hc hu]
  exact h

/-! ### R4. `fun_prop` · closes a differentiability goal, using `hf : ContDiff ℝ 2 f` from the context
`f` is C², so `fderiv ℝ f` is C¹, hence differentiable; a constant function is differentiable. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (x v : E) : DifferentiableAt ℝ (fun y => fderiv ℝ f y) x ∧ DifferentiableAt ℝ (fun _ : E => v) x :=
  ⟨by fun_prop, by fun_prop⟩

/-! ## Cleaning up (`simp` applies R5–R7 by itself) -/

/-! ### R5. `fderiv_fun_const`, `Pi.zero_apply` · goal: derivative of a constant → `0` -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (v x : E) (P : (E →L[ℝ] E) → Prop)
    (h : P 0) : P (fderiv ℝ (fun _ : E => v) x) := by
  simp only [fderiv_fun_const, Pi.zero_apply]
  exact h

/-! ### R6. `ContinuousLinearMap.comp_zero`, `zero_add` · goal: `A ∘L 0 + B` → `0 + B` → `B` -/
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A B : E →L[ℝ] F) (P : (E →L[ℝ] F) → Prop) (h : P B) :
    P (A ∘L (0 : E →L[ℝ] E) + B) := by
  rw [ContinuousLinearMap.comp_zero]
  rw [zero_add]
  exact h

/-! ### R7. `ContinuousLinearMap.flip_apply` · goal: `A.flip v w` → `A w v` (swap the two arguments) -/
example {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (A : E →L[ℝ] F →L[ℝ] G) (v : F)
    (w : E) (P : G → Prop) (h : P (A w v)) : P (A.flip v w) := by
  rw [ContinuousLinearMap.flip_apply]
  exact h

/-! ## Symmetry of the second derivative (Schwarz) -/

/-! ### R8. `ContDiff.contDiffAt` · context gains `ContDiffAt ℝ n f x` (C^n near the point `x`) -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (x : E) (G : Prop) (k : ContDiffAt ℝ 2 f x → G) : G := by
  have hx : ContDiffAt ℝ 2 f x := hf.contDiffAt
  exact k hx

/-! ### R9. `ContDiffAt.isSymmSndFDerivAt` · context gains `IsSymmSndFDerivAt ℝ f x`
`ContDiffAt 𝕜 n f x → minSmoothness 𝕜 2 ≤ n → IsSymmSndFDerivAt 𝕜 f x`. Over `ℝ`,
`minSmoothness ℝ 2 = 2`, so `(by simp)` proves the side condition. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E)
    (hx : ContDiffAt ℝ 2 f x) (G : Prop) (k : IsSymmSndFDerivAt ℝ f x → G) : G := by
  have hs := hx.isSymmSndFDerivAt (by simp)
  exact k hs

/-! ### R10. `IsSymmSndFDerivAt.eq` · closes `fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v` -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x v w : E)
    (hs : IsSymmSndFDerivAt ℝ f x) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  exact hs.eq v w

/-! ## Curl and gradient → components -/

/-! ### R11. `unfold Space.curl` · goal: `curl F x` → a vector built component by component
`∇ ⨯ F` is notation for `Space.curl F` and prints as `curl F`. Indices `i + 1`, `i + 2` wrap in `Fin 3`. -/
example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) (P : EuclideanSpace ℝ (Fin 3) → Prop)
    (h : P (WithLp.toLp 2 fun i =>
      ∂[i + 1] (fun y => (F y).ofLp (i + 2)) x - ∂[i + 2] (fun y => (F y).ofLp (i + 1)) x)) :
    P ((∇ ⨯ F) x) := by
  unfold Space.curl
  exact h

/-! ### R12. `unfold Space.grad` · goal: `∇ f x` → the vector with components `∂[i] f x` -/
example (f : Space → ℝ) (x : Space) (P : EuclideanSpace ℝ (Fin 3) → Prop)
    (h : P (WithLp.toLp 2 fun i => ∂[i] f x)) : P (∇ f x) := by
  unfold Space.grad
  exact h

/-! ### R13. `ext i` (lemma `PiLp.ext`) · goal `v = w` in `EuclideanSpace ℝ (Fin 3)` → component `i` -/
example (v w : EuclideanSpace ℝ (Fin 3)) (h : ∀ i, v.ofLp i = w.ofLp i) : v = w := by
  ext i
  exact h i

/-! ### R14. `simp only []` · goal: inlines `have k := …;` and cancels `(WithLp.toLp 2 g).ofLp i` → `g i` -/
example (g : Fin 3 → ℝ) (i : Fin 3) (P : ℝ → Prop) (h : P (g i)) :
    P ((have k := g; (WithLp.toLp 2 k : EuclideanSpace ℝ (Fin 3))).ofLp i) := by
  simp only []
  exact h

/-! ### R15. `PiLp.zero_apply` · goal: component `i` of the zero vector, `WithLp.ofLp 0 i` → `0` -/
example (i : Fin 3) (P : ℝ → Prop) (h : P 0) : P ((0 : EuclideanSpace ℝ (Fin 3)).ofLp i) := by
  rw [PiLp.zero_apply]
  exact h

/-! ## Finishing -/

/-! ### R16. `rw [hg]` with `hg : ∀ a b, g a b = g b a` · goal: only the FIRST match is rewritten
`rw` fixes `a, b` from the first instance it finds and rewrites only that instance. -/
example (g : Fin 3 → Fin 3 → ℝ) (hg : ∀ a b, g a b = g b a) (i : Fin 3) (P : ℝ → Prop)
    (h : P (g (i + 2) (i + 1) - g (i + 2) (i + 1))) : P (g (i + 1) (i + 2) - g (i + 2) (i + 1)) := by
  rw [hg]
  exact h

/-! ### R17. `simp` (lemma `sub_self : a - a = 0`) · closes `a - a = 0`, also when one copy is η-expanded
`fun y => g y` and `g` are the same function (η), so `simp` sees `a - a`. -/
example (μ : Fin 3) (g : Space → ℝ) (x : Space) : ∂[μ] g x - ∂[μ] (fun y => g y) x = 0 := by
  simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The curl of a constant field is zero: R11, R13, R14 + R15, then R2 and R5 via `simp` -/
example (v : EuclideanSpace ℝ (Fin 3)) (x : Space) : (∇ ⨯ (fun _ => v)) x = 0 := by
  unfold Space.curl
  ext i
  simp only [PiLp.zero_apply]
  simp [Space.deriv_eq]

/-! ### W2. A difference of two swapped entries of a symmetric table: R16, then R17 -/
example (g : Fin 3 → Fin 3 → ℝ) (hg : ∀ a b, g a b = g b a) (i : Fin 3) :
    g (i + 1) (i + 2) - g (i + 2) (i + 1) = 0 := by
  rw [hg]
  simp

/-! ### W3. Schwarz on an arbitrary normed space, as one term: R8 → R9 → R10 -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℝ) (hg : ContDiff ℝ 2 g)
    (x v w : E) : fderiv ℝ (fderiv ℝ g) x v w = fderiv ℝ (fderiv ℝ g) x w v :=
  (hg.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

end M182Guide

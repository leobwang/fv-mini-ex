/- Guide for H106 (Gauss's law for magnetism from the vector potential).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (scalar fields, plain sums).
Assumed: Lean basics (E001–E033). The infoview prints `∂[μ] f` as `Space.deriv μ f`, `∇ ⬝ F` as
`Space.div F`, `∇ ⨯ F` as `curl F`, and the component `F x i` as `(F x).ofLp i`.
-/
import Physlib.Electromagnetism.ThreeDimension.Basic

open Electromagnetism ElectromagneticPotential Space Time ContDiff

namespace H106Guide

/-! # Part R · Reference entries -/

/-! ## Smoothness facts: components and derivatives -/

/-! ### R1. `contDiff_euclidean` · context gains: a `Cⁿ` vector field has `Cⁿ` components
`contDiff_euclidean : ContDiff ℝ n F ↔ ∀ i, ContDiff ℝ n (fun x => F x i)`; `.mp` is the `→` half. -/
example {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] {n : WithTop ℕ∞}
    (F : E → EuclideanSpace ℝ ι) (hF : ContDiff ℝ n F) (i : ι) (G : Prop)
    (g : ContDiff ℝ n (fun x => F x i) → G) : G := by
  have hi : ContDiff ℝ n (fun x => F x i) := contDiff_euclidean.mp hF i
  exact g hi

/-! ### R2. `Space.deriv_eq_fderiv_fun` · goal: the function `∂[μ] f` → `fun x => fderiv ℝ f x (basis μ)`
Used inside `Differentiable ℝ (∂[μ] f)`, so that `fun_prop` (R3) can read the goal. -/
example (f : Space → ℝ) (μ : Fin 3) (h : Differentiable ℝ fun x => fderiv ℝ f x (Space.basis μ)) :
    Differentiable ℝ (∂[μ] f) := by
  rw [Space.deriv_eq_fderiv_fun]
  exact h

/-! ### R3. `fun_prop` · closes `Differentiable ℝ (fun x => fderiv ℝ f x v)` from `hf : ContDiff ℝ 2 f`
A `C²` function has a `C¹` (hence differentiable) derivative; `fun_prop` finds `hf` in the context. -/
example (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (μ : Fin 3) :
    Differentiable ℝ fun x => fderiv ℝ f x (Space.basis μ) := by
  fun_prop

/-! ## Pointwise: from `∂` to `fderiv`, and the derivative of a difference -/

/-! ### R4. `ext x` (lemma `funext`) · goal `F = G` between functions → context gains `x`, goal `F x = G x` -/
example (F G : Space → ℝ) (h : ∀ x, F x = G x) : F = G := by
  ext x
  exact h x

/-! ### R5. `Pi.sub_apply` · `(f - g) x = f x - g x` · goal: apply a difference of functions -/
example (f g : Space → ℝ) (x : Space) (P : ℝ → Prop) (h : P (f x - g x)) : P ((f - g) x) := by
  rw [Pi.sub_apply]
  exact h

/-! ### R6. `Space.deriv_eq` · `∂[μ] f x = fderiv ℝ f x (Space.basis μ)` · goal: one `∂` → `fderiv`
`rw` rewrites every copy of the FIRST match only; each `∂[μ] g x` with a different `g` needs its own
`rw [Space.deriv_eq]`. -/
example (f g : Space → ℝ) (μ : Fin 3) (x : Space) (P : ℝ → ℝ → Prop)
    (h : P (fderiv ℝ f x (Space.basis μ)) (∂[μ] g x)) : P (∂[μ] f x) (∂[μ] g x) := by
  rw [Space.deriv_eq]
  exact h

/-! ### R7. `hg x` · context gains `DifferentiableAt ℝ g x` from `hg : Differentiable ℝ g`
`Differentiable ℝ g` is by definition `∀ x, DifferentiableAt ℝ g x`: apply it to a point. -/
example (g : Space → ℝ) (hg : Differentiable ℝ g) (x : Space) (G : Prop)
    (k : DifferentiableAt ℝ g x → G) : G := by
  have hx : DifferentiableAt ℝ g x := hg x
  exact k hx

/-! ### R8. `fderiv_fun_sub` · derivative of a difference · goal: `fderiv (fun y => f y - g y)` splits
`fderiv_fun_sub : DifferentiableAt ℝ f x → DifferentiableAt ℝ g x →
  fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x`. -/
example (f g : Space → ℝ) (x : Space) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (P : (Space →L[ℝ] ℝ) → Prop) (h : P (fderiv ℝ f x - fderiv ℝ g x)) :
    P (fderiv ℝ (fun y => f y - g y) x) := by
  rw [fderiv_fun_sub hf hg]
  exact h

/-! ### R9. `rfl` · closes `(L₁ - L₂) v = L₁ v - L₂ v` for continuous linear maps (true by definition) -/
example (L₁ L₂ : Space →L[ℝ] ℝ) (v : Space) : (L₁ - L₂) v = L₁ v - L₂ v := by
  rfl

/-! ## Unfolding `∇ ⬝` and `∇ ⨯` -/

/-! ### R10. `simp only [Space.div]` · goal: `∇ ⬝ F` at `x` → the sum `∑ i, ∂[i] (F · i) x` -/
example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) (P : ℝ → Prop)
    (h : P (∑ i, ∂[i] (fun y => F y i) x)) : P ((∇ ⬝ F) x) := by
  simp only [Space.div]
  exact h

/-! ### R11. `simp only [Space.curl]` · goal: component `i` of `∇ ⨯ F` → `∂[i+1] F_{i+2} - ∂[i+2] F_{i+1}` -/
example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) (i : Fin 3) (P : ℝ → Prop)
    (h : P (∂[i + 1] (fun y => F y (i + 2)) x - ∂[i + 2] (fun y => F y (i + 1)) x)) :
    P ((∇ ⨯ F) x i) := by
  simp only [Space.curl]
  exact h

/-! ### R12. `Fin.sum_univ_three` · `∑ i, f i = f 0 + f 1 + f 2` · goal: a sum over `Fin 3` → three terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 3 → β) (P : β → Prop) (h : P (f 0 + f 1 + f 2)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_three]
  exact h

/-! ### R13. `simp only [Fin.isValue, Fin.reduceAdd, zero_add]` · goal: index arithmetic in `Fin 3`
`Fin.reduceAdd` computes `a + b` of numerals mod 3 (`2 + 2 = 1`); `zero_add` does `0 + a = a`;
`Fin.isValue` only tags numerals so they print as `0, 1, 2`. -/
example {β : Type} (a : Fin 3 → β) (P : β → β → β → Prop) (h : P (a 1) (a 0) (a 1)) :
    P (a (0 + 1)) (a (1 + 2)) (a (2 + 2)) := by
  simp only [Fin.isValue, Fin.reduceAdd, zero_add]
  exact h

/-! ## Schwarz and the cancellation -/

/-! ### R14. `Space.deriv_commute` · `ContDiff ℝ 2 f → ∂[u] (∂[v] f) = ∂[v] (∂[u] f)` · goal: swap two `∂`
`u v` are implicit: `rw [Space.deriv_commute _ hf]` swaps the FIRST `∂[u] (∂[v] f)` it meets (any `u v`)
and every identical copy; a later copy of the swapped form `∂[v] (∂[u] f)` is left alone. -/
example (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (u v : Fin 3) (x : Space) (P : ℝ → Prop)
    (h : P (∂[v] (∂[u] f) x)) : P (∂[u] (∂[v] f) x) := by
  rw [Space.deriv_commute _ hf]
  exact h

/-! ### R15. `ring` · closes an identity of commutative rings; each `∂[…] … x` is just an unknown -/
example (a b c : ℝ) : a - b + (c - a) + (b - c) = 0 := by
  ring

/-! ## The magnetic field -/

/-! ### R16. `ThreeDimension.magneticField_eq_3D` · goal: `magneticField c V` → `fun t x => (∇ ⨯ A t) x`
Here `A t = vectorPotential c V t : Space → EuclideanSpace ℝ (Fin 3)` is the vector potential at time `t`. -/
example (c : SpeedOfLight) (V : ElectromagneticPotential)
    (P : (Time → Space → EuclideanSpace ℝ (Fin 3)) → Prop)
    (h : P (fun t x => (∇ ⨯ V.vectorPotential c t) x)) : P (V.magneticField c) := by
  rw [ThreeDimension.magneticField_eq_3D]
  exact h

/-! ### R17. `fun_prop` · closes `ContDiff ℝ n (V.vectorPotential c t)` from `hV : ContDiff ℝ ∞ V`
physlib tags `vectorPotential_contDiff_of_smooth` with `@[fun_prop]`; `fun_prop` then fixes `t`. -/
example (V : ElectromagneticPotential) (hV : ContDiff ℝ ∞ V) (c : SpeedOfLight) (t : Time) :
    ContDiff ℝ 1 (V.vectorPotential c t) := by
  fun_prop

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A difference of two differentiable functions: R4, R5, R6 (three times), R7, R8, R9 -/
example (g k : Space → ℝ) (hg : Differentiable ℝ g) (hk : Differentiable ℝ k) (u : Fin 3) :
    ∂[u] (fun x => g x - k x) = ∂[u] g - ∂[u] k := by
  ext x
  rw [Pi.sub_apply, Space.deriv_eq, Space.deriv_eq, Space.deriv_eq]
  rw [fderiv_fun_sub (hg x) (hk x)]
  rfl

/-! ### W2. Mixed partials of a scalar field cancel: R14, then R15 -/
example (g : Space → ℝ) (hg : ContDiff ℝ 2 g) (x : Space) :
    ∂[0] (∂[1] g) x - ∂[1] (∂[0] g) x = 0 := by
  rw [Space.deriv_commute _ hg]
  ring

/-! ### W3. A cyclic sum over `Fin 3`: R12, R13, then R15 -/
example (a : Fin 3 → ℝ) : ∑ i, (a (i + 1) - a i) = 0 := by
  simp only [Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd, zero_add]
  ring

end H106Guide

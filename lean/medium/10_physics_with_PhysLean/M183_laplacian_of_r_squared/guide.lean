/- Guide for M183 (Laplacian of r²).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the coordinate function `y ↦ yᵢ`,
the function `y ↦ 3 yᵢ`, an abstract table `F : Fin n → ℝ`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.SpaceAndTime.Space.Derivatives.Laplacian

open Space

namespace M183Guide

/-! # Part R · Reference entries -/

/-! ## A first derivative, as a function -/

/-! ### R1. `funext y` · goal `f = g` (functions) → context gains `y`, goal `f y = g y` -/
example {α β : Type} (f g : α → β) (h : ∀ y, f y = g y) : f = g := by
  funext y
  exact h y

/-! ### R2. `Space.deriv_norm_sq` · goal: `∂[i] (fun x => ‖x‖ ^ 2) y` → `2 * y.val i`
`∀ {d} (x : Space d) (i : Fin d), ∂[i] (fun x => ‖x‖ ^ 2) x = 2 * x.val i`: ∂(r²)/∂yᵢ = 2yᵢ. -/
example {d : ℕ} (i : Fin d) (y : Space d) (P : ℝ → Prop) (h : P (2 * y.val i)) :
    P (∂[i] (fun x : Space d => ‖x‖ ^ 2) y) := by
  rw [Space.deriv_norm_sq]
  exact h

/-! ## A partial derivative → a Fréchet derivative, and back -/

/-! ### R3. `Space.deriv_eq` · goal: the NUMBER `∂[μ] f x` → `fderiv ℝ f x (basis μ)` -/
example {d : ℕ} (μ : Fin d) (f : Space d → ℝ) (x : Space d) (P : ℝ → Prop)
    (h : P ((fderiv ℝ f x) (basis μ))) : P (∂[μ] f x) := by
  rw [Space.deriv_eq]
  exact h

/-! ### R4. `fderiv_const_mul` · goal: derivative of `fun y => b * a y` → `b • fderiv ℝ a x`
`DifferentiableAt 𝕜 a x → ∀ b, fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x`. Without its
argument, `rw` adds the side goal `DifferentiableAt ℝ a x` after the main goal (goal list grows). -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → ℝ) (b : ℝ) (x : E)
    (P : (E →L[ℝ] ℝ) → Prop) (h : P (b • fderiv ℝ a x)) (ha : DifferentiableAt ℝ a x) :
    P (fderiv ℝ (fun y => b * a y) x) := by
  rw [fderiv_const_mul]
  exact h
  exact ha

/-! ### R5. `fun_prop` · closes `DifferentiableAt ℝ (fun y => y.val i) x` (a coordinate is linear) -/
example {d : ℕ} (i : Fin d) (x : Space d) : DifferentiableAt ℝ (fun y : Space d => y i) x := by
  fun_prop

/-! ### R6. `_root_.smul_apply`, `smul_eq_mul` · goal: `(c • A) v` → `c • A v` → `c * A v`
Under `open Space`, a bare `smul_apply` means `Space.smul_apply` (about `(c • y).val i`); write
`_root_.smul_apply` for the general lemma. `simp` finds the right one by itself. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E →L[ℝ] ℝ) (c : ℝ) (v : E)
    (P : ℝ → Prop) (h : P (c * A v)) : P ((c • A) v) := by
  rw [_root_.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R7. `← Space.deriv_eq` · goal: `fderiv ℝ f x (basis μ)` → back to `∂[μ] f x` -/
example {d : ℕ} (μ : Fin d) (f : Space d → ℝ) (x : Space d) (P : ℝ → Prop) (h : P (∂[μ] f x)) :
    P ((fderiv ℝ f x) (basis μ)) := by
  rw [← Space.deriv_eq]
  exact h

/-! ### R8. `Space.deriv_component_same` · goal: `∂[μ] (fun x => x.val μ) x` → `1` (∂yμ/∂yμ = 1)
The general form is `Space.deriv_component : ∂[ν] (fun x => x.val μ) x = if ν = μ then 1 else 0`. -/
example {d : ℕ} (μ : Fin d) (x : Space d) (P : ℝ → Prop) (h : P 1) :
    P (∂[μ] (fun y : Space d => y.val μ) x) := by
  rw [Space.deriv_component_same]
  exact h

/-! ## The Laplacian → a finite sum, and evaluating the sum -/

/-! ### R9. `Space.laplacian_eq_sum_snd_deriv` · goal: `Δ f x` → `(fun x => ∑ i, ∂[i] (∂[i] f) x) x`
The lemma is an equation of FUNCTIONS, `Δ f = fun x => ∑ i, ∂[i] (∂[i] f) x`, so after `rw` the point
`x` is applied to a `fun`; any `simp` β-reduces that to `∑ i, ∂[i] (∂[i] f) x`. -/
example {d : ℕ} (f : Space d → ℝ) (x : Space d) (P : ℝ → Prop)
    (h : P ((fun x => ∑ i, ∂[i] (∂[i] f) x) x)) : P (Δ f x) := by
  rw [laplacian_eq_sum_snd_deriv]
  exact h

/-! ### R10. `simp only [hFG]` with `hFG : ∀ i, F i = G i` · goal: rewrites UNDER the binder of `∑ i`
`rw` cannot rewrite a term that mentions the bound `i`; `simp` can. -/
example {n : ℕ} (F G : Fin n → ℝ) (hFG : ∀ i, F i = G i) (P : ℝ → Prop) (h : P (∑ i, G i)) :
    P (∑ i, F i) := by
  simp only [hFG]
  exact h

/-! ### R11. `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin` · goal: `∑ _i : Fin n, c` → `n • c` -/
example {n : ℕ} (c : ℝ) (P : ℝ → Prop) (h : P (n • c)) : P (∑ _i : Fin n, c) := by
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [Fintype.card_fin]
  exact h

/-! ### R12. `nsmul_eq_mul` · goal: `n • a` (n-fold sum, `n : ℕ`) → `↑n * a` (product in `ℝ`) -/
example (n : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (↑n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R13. `ring` · closes a commutative-ring identity; the cast `↑n` is just an unknown to it -/
example (n : ℕ) (a : ℝ) : ↑n * a = a * ↑n := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A first derivative as a function: R1, then a derivative lemma (here R8's) -/
example {d : ℕ} (i : Fin d) : ∂[i] (fun y : Space d => y i) = fun _ => 1 := by
  funext y
  exact deriv_component_same i y

/-! ### W2. ∂(3 yᵢ)/∂yᵢ = 3, step by step: R3, R4 + R5, R6, R7, R8, then R13 -/
example {d : ℕ} (i : Fin d) (x : Space d) : ∂[i] (fun y : Space d => 3 * y i) x = 3 := by
  rw [Space.deriv_eq, fderiv_const_mul (by fun_prop)]
  rw [_root_.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq]
  rw [deriv_component_same]
  ring

/-! ### W3. The same in one `simp`: it applies R6, R7 (given as `← Space.deriv_eq`), R8 and `mul_one` -/
example {d : ℕ} (i : Fin d) (x : Space d) : ∂[i] (fun y : Space d => 3 * y i) x = 3 := by
  rw [Space.deriv_eq, fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq]

/-! ### W4. A sum of a constant table: `simp [hF]` does R10, R11, R12; R13 finishes -/
example {n : ℕ} (F : Fin n → ℝ) (hF : ∀ i, F i = 5) : ∑ i, F i = 5 * n := by
  simp [hF]
  ring

end M183Guide

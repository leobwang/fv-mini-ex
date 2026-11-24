/- Guide for M184 (Curl of a rigid rotation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a single scaled coordinate
`c * y_k`, the stretched position field `y ↦ c • y`, a general cross product `u × v`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.SpaceAndTime.Space.Derivatives.Curl

open Space Matrix

namespace M184Guide

/-! # Part R · Reference entries -/

/-! ## Partial derivatives `∂[μ]` → Fréchet derivatives `fderiv`, and back -/

/-! ### R1. `Space.deriv_eq` · goal: the number `∂[μ] f x` → `fderiv ℝ f x (basis μ)`
`∂[μ] f x` is notation for `Space.deriv μ f x` and prints that way. -/
example (μ : Fin 3) (f : Space → ℝ) (x : Space) (P : ℝ → Prop)
    (h : P ((fderiv ℝ f x) (basis μ))) : P (∂[μ] f x) := by
  rw [Space.deriv_eq]
  exact h

/-! ### R2. `fderiv_fun_sub` · goal: derivative of `fun y => f y - g y` → difference of derivatives
`DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x`.
Without arguments, `rw` adds the two differentiability side goals to the goal list. -/
example (x : Space) (f g : Space → ℝ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (P : (Space →L[ℝ] ℝ) → Prop) (h : P (fderiv ℝ f x - fderiv ℝ g x)) :
    P (fderiv ℝ (fun y => f y - g y) x) := by
  rw [fderiv_fun_sub]
  exacts [h, hf, hg]

/-! ### R3. `fun_prop` · closes a goal `DifferentiableAt ℝ f x` built from coordinates, `*`, `-`, constants
Pass it as an argument: `rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]`. -/
example (c : ℝ) (k l : Fin 3) (x : Space) :
    DifferentiableAt ℝ (fun y : Space => c * y.val k - y.val l) x := by fun_prop

/-! ### R4. `fderiv_const_mul` · goal: derivative of `fun y => b * a y` → `b • fderiv ℝ a x`
`DifferentiableAt ℝ a x → ∀ b, fderiv ℝ (fun y => b * a y) x = b • fderiv ℝ a x`. -/
example (x : Space) (b : ℝ) (a : Space → ℝ) (ha : DifferentiableAt ℝ a x)
    (P : (Space →L[ℝ] ℝ) → Prop) (h : P (b • fderiv ℝ a x)) :
    P (fderiv ℝ (fun y => b * a y) x) := by
  rw [fderiv_const_mul ha]
  exact h

/-! ### R5. `_root_.sub_apply` · goal: `(L₁ - L₂) v` → `L₁ v - L₂ v` for linear maps
`open Space` makes plain `sub_apply` mean `Space.sub_apply` (points of space); `_root_.` picks the
general lemma. -/
example (L₁ L₂ : Space →L[ℝ] ℝ) (v : Space) (P : ℝ → Prop) (h : P (L₁ v - L₂ v)) :
    P ((L₁ - L₂) v) := by
  rw [_root_.sub_apply]
  exact h

/-! ### R6. `_root_.smul_apply` · goal: `(c • L) v` → `c • L v` -/
example (L : Space →L[ℝ] ℝ) (c : ℝ) (v : Space) (P : ℝ → Prop) (h : P (c • L v)) :
    P ((c • L) v) := by
  rw [_root_.smul_apply]
  exact h

/-! ### R7. `smul_eq_mul` · goal: `c • r` → `c * r` when both are numbers -/
example (c r : ℝ) (P : ℝ → Prop) (h : P (c * r)) : P (c • r) := by
  rw [smul_eq_mul]
  exact h

/-! ### R8. `← Space.deriv_eq` · goal: `fderiv ℝ f x (basis μ)` → back to `∂[μ] f x` -/
example (μ : Fin 3) (f : Space → ℝ) (x : Space) (P : ℝ → Prop) (h : P (∂[μ] f x)) :
    P ((fderiv ℝ f x) (basis μ)) := by
  rw [← Space.deriv_eq]
  exact h

/-! ### R9. `Space.deriv_component` · goal: `∂[ν]` of the coordinate `y ↦ y_μ` → Kronecker delta -/
example (μ ν : Fin 3) (x : Space) (P : ℝ → Prop) (h : P (if ν = μ then 1 else 0)) :
    P (∂[ν] (fun y : Space => y.val μ) x) := by
  rw [deriv_component]
  exact h

/-! ## A vector equation → three component equations -/

/-! ### R10. `ext i` · goal `u = v` in `EuclideanSpace ℝ (Fin 3)` → component `i` -/
example (u v : EuclideanSpace ℝ (Fin 3)) (h : ∀ i, u.ofLp i = v.ofLp i) : u = v := by
  ext i
  exact h i

/-! ### R11. `fin_cases i` · context loses `i : Fin 3`; goal → three goals, one per value of `i` -/
example (P : Fin 3 → Prop) (i : Fin 3) (h0 : P 0) (h1 : P 1) (h2 : P 2) : P i := by
  fin_cases i
  exacts [h0, h1, h2]

/-! ## Evaluating one component (`simp` applies R13, R14, R16–R19 by itself) -/

/-! ### R12. `Space.curl` · goal: component `i` of `∇ ⨯ F` → two partial derivatives
`∇ ⨯ F` is notation for `Space.curl F` and prints as `curl F`. Indices are `Fin 3`, so `i + 1` and
`i + 2` wrap around mod 3. -/
example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) (i : Fin 3) (P : ℝ → Prop)
    (h : P (∂[i + 1] (fun x => (F x).ofLp (i + 2)) x - ∂[i + 2] (fun x => (F x).ofLp (i + 1)) x)) :
    P ((curl F x).ofLp i) := by
  simp only [curl]
  exact h

/-! ### R13. `Fin.reduceAdd` · goal: arithmetic on literal `Fin 3` indices, mod 3 -/
example (P : Fin 3 → Prop) (h : P 1) : P ((2 : Fin 3) + 2) := by
  simp only [Fin.reduceAdd]
  exact h

/-! ### R14. `WithLp.equiv_apply`, `WithLp.equiv_symm_apply` · goal: unwrap the notation `u ⨯ₑ₃ v`
`u ⨯ₑ₃ v` is notation for a `fun a b => …` that converts to plain functions `Fin 3 → ℝ`, takes
`crossProduct`, and converts back. These two lemmas remove the conversions. -/
example (u v : EuclideanSpace ℝ (Fin 3)) (P : ℝ → Prop)
    (h : P ((crossProduct u.ofLp) v.ofLp 0)) : P ((u ⨯ₑ₃ v).ofLp 0) := by
  simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]
  exact h

/-! ### R15. `cross_apply` · goal: `crossProduct a b` → the vector literal of its three components -/
example (a b : Fin 3 → ℝ) (P : (Fin 3 → ℝ) → Prop)
    (h : P ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]) :
    P ((crossProduct a) b) := by
  rw [cross_apply]
  exact h

/-! ### R16. `Matrix.cons_val_…` (via `simp`) · goal: entry of a vector literal `![a, b, c] k` -/
example {α : Type} (a b c : α) (P : α → Prop) (h : P c) : P (![a, b, c] 2) := by
  simp
  exact h

/-! ### R17. `Space.basis_repr_apply` · goal: component of `basis.repr p` → coordinate of `p` -/
example (p : Space) (i : Fin 3) (P : ℝ → Prop) (h : P (p.val i)) : P ((basis.repr p).ofLp i) := by
  rw [basis_repr_apply]
  exact h

/-! ### R18. `Fin.reduceEq`, `↓reduceIte` (via `simp`) · goal: `if` on literal indices → one branch -/
example {α : Type} (a b : α) (P : α → Prop) (h : P b) : P (if (1 : Fin 3) = 0 then a else b) := by
  simp only [Fin.reduceEq, ↓reduceIte]
  exact h

/-! ### R19. `PiLp.smul_apply` · goal: component of `c • v` → `c • v.ofLp i`; then R7 -/
example (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) (P : ℝ → Prop) (h : P (c * v.ofLp i)) :
    P ((c • v).ofLp i) := by
  rw [PiLp.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R20. `ring` · closes an identity of commutative rings such as `a + a = 2 * a` -/
example (a : ℝ) : a + a = 2 * a := by ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. One scaled coordinate: R1 → R4 (side goal by R3) → R6 → R7 → R8 → R9 -/
theorem deriv_coord_mul (c : ℝ) (j k : Fin 3) (x : Space) :
    ∂[j] (fun y : Space => c * y.val k) x = c * (if j = k then 1 else 0) := by
  rw [Space.deriv_eq]
  rw [fderiv_const_mul (by fun_prop)]
  rw [_root_.smul_apply]
  rw [smul_eq_mul]
  rw [← Space.deriv_eq]
  rw [deriv_component]

/-! ### W2. Without a derivative lemma, `simp` stops at `∂[μ] (fun y => …)`
`∇ ⨯ (y ↦ c • y) = 0`. `simp [curl, basis_repr_apply]` evaluates everything except the partial
derivatives of `fun y => c * y_k`; W1 in the simp set finishes. -/
example (c : ℝ) (x : Space) : (∇ ⨯ fun y : Space => c • basis.repr y) x = 0 := by
  ext i
  fin_cases i
  all_goals simp [curl, basis_repr_apply]
  all_goals simp [deriv_coord_mul]

/-! ### W3. A cross-product component: R14 → R15 → R16 -/
example (u v : EuclideanSpace ℝ (Fin 3)) :
    (u ⨯ₑ₃ v).ofLp 1 = u.ofLp 2 * v.ofLp 0 - u.ofLp 0 * v.ofLp 2 := by
  simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]
  rw [cross_apply]
  simp

end M184Guide

/- Guide for E075 (fun_prop).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`u v : ℝ → ℝ` stand for arbitrary real functions; a hypothesis such as `hu : Continuous u` is only there
to finish the example.
`fun_prop` (R1, R8, R12, R17) is the one tactic the exercise needs. The other entries are the lemmas it
applies for you, one at a time with `apply`, so you can see what it does and read its error messages.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E075Guide

/-! # Part R · Reference entries -/

/-! ## Continuity of a function built from pieces -/

/-! ### R1. `fun_prop` · closes `Continuous (fun x => …)` when the body is built from `+`, `*`, `^`,
constants and `x` -/
example (c : ℝ) (n : ℕ) : Continuous (fun x : ℝ => c * x ^ n + x) := by
  fun_prop

/-! ### R2. `apply Continuous.add` · goal list: `Continuous (fun x => u x + v x)` → `Continuous u`,
`Continuous v` -/
example (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) : Continuous (fun x => u x + v x) := by
  apply Continuous.add
  exacts [hu, hv]

/-! ### R3. `apply Continuous.mul` · goal list: `Continuous (fun x => u x * v x)` → `Continuous u`,
`Continuous v` -/
example (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) : Continuous (fun x => u x * v x) := by
  apply Continuous.mul
  exacts [hu, hv]

/-! ### R4. `continuous_const` · closes `Continuous (fun x => c)` (a constant function) -/
example (c : ℝ) : Continuous (fun _ : ℝ => c) := by
  exact continuous_const

/-! ### R5. `continuous_id` · closes `Continuous (fun x => x)` (stated as `Continuous id`) -/
example : Continuous (fun x : ℝ => x) := by
  exact continuous_id

/-! ### R6. `continuous_pow n` · closes `Continuous (fun x => x ^ n)` -/
example (n : ℕ) : Continuous (fun x : ℝ => x ^ n) := by
  exact continuous_pow n

/-! ### R7. `Real.continuous_exp`, `Real.continuous_sin`, `Real.continuous_cos` · close
`Continuous Real.exp` and the like; `fun_prop` knows these by name -/
example : Continuous Real.exp ∧ Continuous Real.sin ∧ Continuous Real.cos := by
  exact ⟨Real.continuous_exp, Real.continuous_sin, Real.continuous_cos⟩

/-! ## Differentiability -/

/-! ### R8. `fun_prop` on `Differentiable ℝ f` · closes it; the field `ℝ` comes first -/
example : Differentiable ℝ (fun x : ℝ => Real.sin x * x ^ 3) := by
  fun_prop

/-! ### R9. `apply Differentiable.mul` · goal list: product → one goal per factor -/
example (u v : ℝ → ℝ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    Differentiable ℝ (fun x => u x * v x) := by
  apply Differentiable.mul
  exacts [hu, hv]

/-! ### R10. `apply Differentiable.comp` (chain rule) · goal list: `fun x => v (u x)` → the outer
function `v` first, then the inner `u`. On a concrete outer function such as `Real.sin`, name it:
`refine Differentiable.comp (g := Real.sin) ?_ ?_` (see W2). -/
example (u v : ℝ → ℝ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    Differentiable ℝ (fun x => v (u x)) := by
  apply Differentiable.comp
  exacts [hv, hu]

/-! ### R11. `Real.differentiable_exp`, `Real.differentiable_cos`, `differentiable_pow n` · close the
basic differentiability goals (also `Real.differentiable_sin`, `differentiable_const c`,
`differentiable_id`) -/
example (n : ℕ) :
    Differentiable ℝ Real.exp ∧ Differentiable ℝ Real.cos ∧ Differentiable ℝ (fun x : ℝ => x ^ n) := by
  exact ⟨Real.differentiable_exp, Real.differentiable_cos, differentiable_pow n⟩

/-! ## Unknown functions given by hypotheses -/

/-! ### R12. `fun_prop` with `hu : Continuous u` in the context · closes; `u` is treated as a known piece -/
example (u : ℝ → ℝ) (hu : Continuous u) : Continuous (fun x => Real.exp (u x) + u x) := by
  fun_prop

/-! ### R13. `apply Continuous.comp` · goal list: `Continuous (fun x => v (u x))` → `Continuous v`,
`Continuous u` -/
example (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) : Continuous (fun x => v (u x)) := by
  apply Continuous.comp
  exacts [hv, hu]

/-! ## Continuity at one point, and side conditions -/

/-! ### R14. `apply ContinuousAt.mul` · goal list: `ContinuousAt (fun x => u x * v x) a` → one goal per
factor, at the same point `a` -/
example (u v : ℝ → ℝ) (a : ℝ) (hu : ContinuousAt u a) (hv : ContinuousAt v a) :
    ContinuousAt (fun x => u x * v x) a := by
  apply ContinuousAt.mul
  exacts [hu, hv]

/-! ### R15. `apply Continuous.continuousAt` · goal: `ContinuousAt u a` → `Continuous u`
(continuous everywhere implies continuous at `a`) -/
example (u : ℝ → ℝ) (a : ℝ) (hu : Continuous u) : ContinuousAt u a := by
  apply Continuous.continuousAt
  exact hu

/-! ### R16. `apply Real.continuousAt_log` · goal: `ContinuousAt Real.log a` → the side goal `a ≠ 0` -/
example (a : ℝ) (ha : a ≠ 0) : ContinuousAt Real.log a := by
  apply Real.continuousAt_log
  exact ha

/-! ### R17. `fun_prop (disch := norm_num)` · closes; every side goal such as `5 ≠ 0` is handed to
`norm_num`. Plain `fun_prop` fails here with "Failed to prove necessary assumption `5 ≠ 0`". -/
example : ContinuousAt (fun x : ℝ => Real.log x + x) 5 := by
  fun_prop (disch := norm_num)

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. A polynomial by hand: R2, R3, R4, R6, R5. `fun_prop` (R1) does all of it. -/
example : Continuous (fun x : ℝ => 5 * x ^ 3 + x) := by
  apply Continuous.add
  · apply Continuous.mul
    · exact continuous_const
    · exact continuous_pow 3
  · exact continuous_id

/-! ### W2. The chain rule by hand, naming the outer function: R10, R11 -/
example : Differentiable ℝ (fun x : ℝ => Real.sin (x ^ 3)) := by
  refine Differentiable.comp (g := Real.sin) ?_ ?_
  · exact Real.differentiable_sin
  · exact differentiable_pow 3

/-! ### W3. Continuity at a point with a side condition by hand: R14, R16, R15, R7.
`fun_prop (disch := norm_num)` (R17) does all of it. -/
example : ContinuousAt (fun x : ℝ => Real.log x * Real.cos x) 3 := by
  apply ContinuousAt.mul
  · apply Real.continuousAt_log
    norm_num
  · apply Continuous.continuousAt
    exact Real.continuous_cos

end E075Guide

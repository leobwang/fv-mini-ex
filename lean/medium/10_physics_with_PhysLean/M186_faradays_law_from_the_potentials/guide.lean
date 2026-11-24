/- Guide for M186 (Faraday's law from the potentials).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: a worked combination on objects that are NOT the exercise's (a gauge transformation).
Assumed: Lean basics.
-/
import Physlib.Electromagnetism.ThreeDimension.Basic

open Electromagnetism ElectromagneticPotential Space Time ContDiff

namespace M186Guide

/-! # Part R · Reference entries -/

/-! ## Fields → potentials -/

/-! ### R1. `ThreeDimension.electricField_eq_3D` · goal: `electricField c U` → `-∇φ - ∂ₜA`
`scalarPotential c U t : Space → ℝ` is φ at time `t`; `vectorPotential c U t : Space → ℝ³` is A. -/
example (U : ElectromagneticPotential) (c : SpeedOfLight)
    (P : (Time → Space → EuclideanSpace ℝ (Fin 3)) → Prop)
    (h : P fun t x => -∇ (U.scalarPotential c t) x - ∂ₜ (fun t => U.vectorPotential c t x) t) :
    P (U.electricField c) := by
  rw [ThreeDimension.electricField_eq_3D]
  exact h

/-! ### R2. `ThreeDimension.magneticField_eq_3D` · goal: `magneticField c U` → `curl A` -/
example (U : ElectromagneticPotential) (c : SpeedOfLight)
    (P : (Time → Space → EuclideanSpace ℝ (Fin 3)) → Prop)
    (h : P fun t x => curl (U.vectorPotential c t) x) :
    P (U.magneticField c) := by
  rw [ThreeDimension.magneticField_eq_3D]
  exact h

/-! ## Rewriting the curl (each rewrite appends side goals) -/

/-! ### R3. `Space.fun_curl_sub` · goal: `curl (f - g)` → `curl f - curl g`; goal list gains
`Differentiable ℝ f` and `Differentiable ℝ g`, AFTER the main goal. -/
example (f g : Space → EuclideanSpace ℝ (Fin 3)) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (P : (Space → EuclideanSpace ℝ (Fin 3)) → Prop)
    (h : P fun x => curl f x - curl g x) : P (curl fun x => f x - g x) := by
  rw [fun_curl_sub]
  exact h
  exact hf
  exact hg

/-! ### R4. `Space.fun_curl_neg` · goal: `curl (-f)` → `-curl f`; goal list gains `Differentiable ℝ f` -/
example (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : Differentiable ℝ f)
    (P : (Space → EuclideanSpace ℝ (Fin 3)) → Prop) (h : P fun x => -curl f x) :
    P (curl fun x => -f x) := by
  rw [fun_curl_neg]
  exact h
  exact hf

/-! ### R5. `Space.curl_of_grad_eq_zero` · goal: `curl (∇ φ)` → `0`; goal list gains `ContDiff ℝ 2 φ` -/
example (φ : Space → ℝ) (hφ : ContDiff ℝ 2 φ) (P : (Space → EuclideanSpace ℝ (Fin 3)) → Prop)
    (h : P 0) : P (curl (∇ φ)) := by
  rw [curl_of_grad_eq_zero]
  exact h
  exact hφ

/-! ### R6. `Space.time_deriv_curl_commute` · goal: `∂ₜ (curl fₜ)` → `curl (∂ₜ fₜ)`; goal list gains
`ContDiff ℝ 2 ↿fₜ` (`↿fₜ : Time × Space → ℝ³` is `fₜ` uncurried). -/
example (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3)) (t : Time) (x : Space)
    (hf : ContDiff ℝ 2 ↿fₜ) (P : EuclideanSpace ℝ (Fin 3) → Prop)
    (h : P (curl (fun x => ∂ₜ (fun t => fₜ t x) t) x)) : P (∂ₜ (fun t => curl (fₜ t) x) t) := by
  rw [time_deriv_curl_commute]
  exact h
  exact hf

/-! ## Closing the main goal -/

/-! ### R7. `simp` · closes `-0 - a = -a` on functions (uses `Pi.zero_apply`, `neg_zero`, `zero_sub`)
`(fun i => …) x` is a beta-redex left by `rw`; `simp` reduces it too. -/
example (f : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) :
    (fun i => (fun i => -(0 : Space → EuclideanSpace ℝ (Fin 3)) i) i - f i) x = -f x := by
  simp

/-! ## Closing the side goals: `fun_prop` and the lemmas it finds -/

/-! ### R8. `fun_prop` · closes a `Differentiable`/`ContDiff` goal built from registered pieces -/
example (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : Differentiable ℝ f) :
    Differentiable ℝ fun x => -f x := by
  fun_prop

/-! ### R9. `scalarPotential_contDiff_space_of_smooth` · `ContDiff ℝ ∞ U → ContDiff ℝ n (φ at t)`
`fun_prop` applies it by itself, using `hU` from the context. -/
example (U : ElectromagneticPotential) (hU : ContDiff ℝ ∞ U) (c : SpeedOfLight) (t : Time) :
    ContDiff ℝ 2 (U.scalarPotential c t) := by
  apply scalarPotential_contDiff_space_of_smooth
  exact hU

/-! ### R10. `vectorPotential_contDiff_of_smooth` · `ContDiff ℝ ∞ U → ContDiff ℝ n ↿A` -/
example (U : ElectromagneticPotential) (hU : ContDiff ℝ ∞ U) (c : SpeedOfLight) :
    ContDiff ℝ 2 ↿(U.vectorPotential c) := by
  apply vectorPotential_contDiff_of_smooth
  exact hU

/-! ### R11. `Space.contDiff_grad` · goal `ContDiff ℝ n (∇ φ)` → `ContDiff ℝ (n + 1) φ`
`fun_prop` chains it with `ContDiff.differentiable_one` (`C¹ → Differentiable`) to prove
`Differentiable ℝ (∇ φ)` from `C²`. `1 + 1` is `2` by definition, so `exact hφ` closes it. -/
example (φ : Space → ℝ) (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (∇ φ) := by
  apply Space.contDiff_grad
  exact hφ

/-! ### R12. `Space.time_deriv_differentiable_space` · `ContDiff ℝ 2 ↿fₜ → x ↦ ∂ₜ fₜ(·, x) differentiable` -/
example (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3)) (t : Time) (hf : ContDiff ℝ 2 ↿fₜ) :
    Differentiable ℝ fun x => ∂ₜ (fun t => fₜ t x) t := by
  apply Space.time_deriv_differentiable_space
  exact hf

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Gauge invariance of B: `curl (A - ∇χ) = curl A`. R3, R5 rewrite and stack side goals;
`·` + R7 closes the main goal, `all_goals` + R8 the side goals. -/
example (f : Space → EuclideanSpace ℝ (Fin 3)) (χ : Space → ℝ) (hf : Differentiable ℝ f)
    (hχ : ContDiff ℝ 2 χ) : (curl fun x => f x - ∇ χ x) = curl f := by
  rw [fun_curl_sub, curl_of_grad_eq_zero]
  · simp
  all_goals fun_prop

end M186Guide

/- Guide for E096 (Expectation is linear).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (two random variables `f`, `g`;
the constant `3`).
Assumed: Lean basics (E001–E033). New: Mathlib's integral `∫ x, f x ∂μ`, the expectation notation
`μ[f]`, and `Integrable`.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace E096Guide

/-! # Part R · Reference entries -/

/-! ## Integrability side conditions -/

/-! ### R1. `Integrable.const_mul` · `Integrable f μ → Integrable (fun x => c * f x) μ` · goal
`apply Integrable.const_mul` reduces the goal to `Integrable f μ`. As a term with dot notation:
`hf.const_mul c : Integrable (fun x => c * f x) μ` for `hf : Integrable f μ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ) :
    Integrable (fun x => c * f x) μ := by
  apply Integrable.const_mul
  exact hf

/-! ### R2. `integrable_const` · `Integrable (fun _ => c) μ` on a finite measure · closes the goal
It needs `[IsFiniteMeasure μ]` (`μ Set.univ < ∞`), which Lean derives from `[IsProbabilityMeasure μ]`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) :
    Integrable (fun _ => c) μ := by
  exact integrable_const c

/-! ## Rewriting integrals -/

/-! ### R3. `integral_add` · `Integrable f μ → Integrable g μ → ∫ f + g = ∫ f + ∫ g` · goal
Write `rw [integral_add hf hg]`: the two integrability proofs are its explicit arguments. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ x, f x ∂μ + ∫ x, g x ∂μ)) :
    P (∫ x, f x + g x ∂μ) := by
  rw [integral_add hf hg]
  exact h

/-! ### R4. `integral_const_mul` · `∫ x, r * f x ∂μ = r * ∫ x, f x ∂μ` · goal
No integrability needed (both sides are `0` when `f` is not integrable). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (r : ℝ) (f : Ω → ℝ) (P : ℝ → Prop)
    (h : P (r * ∫ x, f x ∂μ)) : P (∫ x, r * f x ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! ## The integral of a constant (`simp` applies R5–R8 by itself) -/

/-! ### R5. `integral_const` · `∫ x, c ∂μ = μ.real Set.univ • c` · goal
Any measure: the integral of a constant is (total mass) times the constant. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (P : ℝ → Prop)
    (h : P (μ.real Set.univ • c)) : P (∫ _x, c ∂μ) := by
  rw [integral_const]
  exact h

/-! ### R6. `probReal_univ` · `μ.real Set.univ = 1` for a probability measure · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ℝ → Prop)
    (h : P 1) : P (μ.real Set.univ) := by
  rw [probReal_univ]
  exact h

/-! ### R7. `smul_eq_mul` · `r • c = r * c` when both are in the same ring (here `ℝ`) · goal -/
example (r c : ℝ) (P : ℝ → Prop) (h : P (r * c)) : P (r • c) := by
  rw [smul_eq_mul]
  exact h

/-! ### R8. `one_mul` · `1 * c = c` · goal -/
example {α : Type} [MulOneClass α] (c : α) (P : α → Prop) (h : P c) : P (1 * c) := by
  rw [one_mul]
  exact h

/-! ### R9. `simp` · applies R5–R8 (and `rfl`) by itself; closes the goal when it is then trivial
`simp?` prints the lemmas it used: here `integral_const, probReal_univ, smul_eq_mul, one_mul`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c u : ℝ) :
    u + ∫ _x, c ∂μ = u + c := by
  simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Two random variables: R3 with an R1 argument, then R4 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun ω => f ω + 2 * g ω] = μ[f] + 2 * μ[g] := by
  rw [integral_add hf (hg.const_mul 2)]
  rw [integral_const_mul]

/-! ### W2. The expectation of a constant, one rewrite at a time: R5, R6, R7, R8 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ[fun _ => (3 : ℝ)] = 3 := by
  rw [integral_const]
  rw [probReal_univ]
  rw [smul_eq_mul]
  rw [one_mul]

end E096Guide

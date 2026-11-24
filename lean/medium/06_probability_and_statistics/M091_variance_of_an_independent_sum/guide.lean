/- Guide for M091 (Variance of an independent sum).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` with `k : T → G` is an arbitrary goal that a `have` leaves untouched.
Part W: worked combinations on objects that are NOT the exercise's (`f - g`, `f ^ 2 + 3 f g`).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M091Guide

/-! # Part R · Reference entries -/

/-! ## Facts from `MemLp` and independence (each is a `have`: the context gains a hypothesis) -/

/-! ### R1. `MemLp.integrable` · context gains `Integrable f μ` from `MemLp f 2 μ`
`MemLp.integrable : 1 ≤ q → MemLp f q μ → Integrable f μ` on a finite measure. Write it with dot
notation, `hf.integrable one_le_two`; `one_le_two : 1 ≤ 2` is the side condition `1 ≤ q`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (G : Prop) (k : Integrable f μ → G) : G := by
  have hi : Integrable f μ := hf.integrable one_le_two
  exact k hi

/-! ### R2. `MemLp.aestronglyMeasurable` · context gains `AEStronglyMeasurable f μ`
`MemLp f p μ` contains a measurability proof; this lemma extracts it. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (G : Prop)
    (k : AEStronglyMeasurable f μ → G) : G := by
  have hm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  exact k hm

/-! ### R3. `IndepFun.integral_mul_eq_mul_integral` · context gains `E[f g] = E[f] E[g]`
`IndepFun.integral_mul_eq_mul_integral : f ⟂ᵢ[μ] g → AEStronglyMeasurable f μ →
  AEStronglyMeasurable g μ → ∫ x, (f * g) x ∂μ = (∫ x, f x ∂μ) * ∫ x, g x ∂μ`.
Its own statement has `(f * g) x`; stating the type with `fun x => f x * g x` gives the same fact
in the form that `integral_const_mul` (R13) leaves in the goal. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hfg : f ⟂ᵢ[μ] g)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ) (G : Prop)
    (k : μ[fun x => f x * g x] = μ[f] * μ[g] → G) : G := by
  have h₀ := hfg.integral_mul_eq_mul_integral hfm hgm
  have h₁ : μ[fun x => f x * g x] = μ[f] * μ[g] := hfg.integral_mul_eq_mul_integral hfm hgm
  exact k h₁

/-! ## Integrability of the pieces -/

/-! ### R4. `MemLp.integrable_sq` · context gains `Integrable (fun x => f x ^ 2) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (G : Prop)
    (k : Integrable (fun x => f x ^ 2) μ → G) : G := by
  have hs : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  exact k hs

/-! ### R5. `MemLp.integrable_mul` · context gains `Integrable (f * g) μ` from two `L²` facts
`MemLp.integrable_mul : MemLp f p μ → MemLp g q μ → Integrable (f * g) μ` when `1/p + 1/q = 1`
(Hölder; Lean finds that side condition for `p = q = 2` by itself). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (G : Prop) (k : Integrable (f * g) μ → G) : G := by
  have hp : Integrable (f * g) μ := hf.integrable_mul hg
  exact k hp

/-! ### R6. `Integrable.const_mul` · context gains `Integrable (fun x => c * u x) μ`
`Integrable.const_mul : Integrable u μ → ∀ c, Integrable (fun x => c * u x) μ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (u : Ω → ℝ) (hu : Integrable u μ) (c : ℝ)
    (G : Prop) (k : Integrable (fun x => c * u x) μ → G) : G := by
  have hc : Integrable (fun x => c * u x) μ := hu.const_mul c
  exact k hc

/-! ### R7. `Integrable.add` · context gains `Integrable (u + v) μ`; state the type to get the `fun` form
Without a type, `hu.add hv` has type `Integrable (u + v) μ` (a sum of functions). Writing the type
`Integrable (fun x => u x + v x) μ` gives the same fact in the form `integral_add` (R12) needs. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (u v : Ω → ℝ) (hu : Integrable u μ)
    (hv : Integrable v μ) (G : Prop) (k : Integrable (fun x => u x + v x) μ → G) : G := by
  have h₀ := hu.add hv
  have h₁ : Integrable (fun x => u x + v x) μ := hu.add hv
  exact k h₁

/-! ## Pointwise operations on functions -/

/-! ### R8. `Pi.pow_apply`, `Pi.add_apply` · goal: `((u + v) ^ n) x` → `(u x + v x) ^ n`
`Pi.pow_apply : (u ^ n) x = u x ^ n`, `Pi.add_apply : (u + v) x = u x + v x`. Use `simp only`:
it also rewrites under the bound variable of `∫ x, …` and of `fun x => …`, where `rw` cannot. -/
example {Ω : Type} (u v : Ω → ℝ) (x : Ω) (P : ℝ → Prop) (h : P ((u x + v x) ^ 2)) :
    P (((u + v) ^ 2) x) := by
  simp only [Pi.pow_apply]
  simp only [Pi.add_apply]
  exact h

/-! ## Variance and the integral rules -/

/-! ### R9. `MemLp.add` · `MemLp f p μ → MemLp g p μ → MemLp (f + g) p μ` (`L²` is closed under `+`)
Usually written inline as an argument: `variance_eq_sub (hf.add hg)`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (G : Prop) (k : MemLp (f + g) 2 μ → G) : G := by
  have hs : MemLp (f + g) 2 μ := hf.add hg
  exact k hs

/-! ### R10. `variance_eq_sub` · goal: `Var[f; μ]` → `E[f²] - (E f)²`
`variance_eq_sub : MemLp f 2 μ → Var[f; μ] = ∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2`
(probability measure). `f ^ 2` is the function `x ↦ f x ^ 2`, applied to `x`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (P : ℝ → Prop) (h : P (∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2)) :
    P (Var[f; μ]) := by
  rw [variance_eq_sub hf]
  exact h

/-! ### R11. `rw [e]` with `e : (fun x => (F ^ 2) x) = fun x => …` · goal: the integrand is replaced
`∫ x, (F ^ 2) x ∂μ` is the integral of the function `fun x => (F ^ 2) x`. A hypothesis `e` that
states this function equal to another one replaces the whole integrand at once. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ) (P : ℝ → Prop)
    (e : (fun x => (F ^ 2) x) = fun x => F x * F x) (h : P (∫ x, F x * F x ∂μ)) :
    P (∫ x, (F ^ 2) x ∂μ) := by
  rw [e]
  exact h

/-! ### R12. `integral_add` · goal: `∫ (u + v)` → `∫ u + ∫ v`
`integral_add : Integrable u μ → Integrable v μ → ∫ a, u a + v a ∂μ = ∫ a, u a ∂μ + ∫ a, v a ∂μ`.
`rw` finds the integrand `fun a => u a + v a` only if `u`, `v` are the functions named in the
two integrability proofs (R7). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (u v : Ω → ℝ) (hu : Integrable u μ)
    (hv : Integrable v μ) (P : ℝ → Prop) (h : P (∫ x, u x ∂μ + ∫ x, v x ∂μ)) :
    P (∫ x, u x + v x ∂μ) := by
  rw [integral_add hu hv]
  exact h

/-! ### R13. `integral_const_mul` · goal: `∫ r * u` → `r * ∫ u` (no integrability needed) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (u : Ω → ℝ) (r : ℝ) (P : ℝ → Prop)
    (h : P (r * ∫ x, u x ∂μ)) : P (∫ x, r * u x ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The integrand identity for `(f - g) ^ 2`: `funext`, R8 (with `Pi.sub_apply`), `ring` -/
example {Ω : Type} (f g : Ω → ℝ) :
    (fun x => ((f - g) ^ 2) x) = fun x => f x ^ 2 - 2 * (f x * g x) + g x ^ 2 := by
  funext x
  simp only [Pi.pow_apply, Pi.sub_apply]
  ring

/-! ### W2. Split `E[f² + 3 f g]`: R4, R5, R6, R7, R12, R13 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    ∫ x, f x ^ 2 + 3 * (f x * g x) ∂μ = ∫ x, f x ^ 2 ∂μ + 3 * ∫ x, f x * g x ∂μ := by
  have i1 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have i2 : Integrable (fun x => 3 * (f x * g x)) μ := (hf.integrable_mul hg).const_mul 3
  rw [integral_add i1 i2]
  rw [integral_const_mul]

/-! ### W3. Independence inside a longer goal: R2, R3, then `rw [hp]` and `ring`
`hp` is displayed with `(fun x => f x * g x) x` but `rw [hp]` still finds `∫ x, f x * g x ∂μ`:
the two differ only by a beta step, which `rw` sees through. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (hfg : f ⟂ᵢ[μ] g) :
    2 * ∫ x, f x * g x ∂μ - μ[f] * μ[g] = μ[f] * μ[g] := by
  have hp : μ[fun x => f x * g x] = μ[f] * μ[g] :=
    hfg.integral_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable
  rw [hp]
  ring

end M091Guide

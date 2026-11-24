/- Guide for M089 (Mean squared error decomposition).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (affine maps of `f`, `x * y`).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M089Guide

/-! # Part R · Reference entries -/

/-! ## Integrability facts (each one is a `have`: the context gains a hypothesis) -/

/-! ### R1. `MemLp.integrable` · context gains `Integrable f μ` from `MemLp f 2 μ`
`hf.integrable one_le_two`: `MemLp f q μ` with `1 ≤ q` on a finite measure gives `Integrable f μ`.
`one_le_two : 1 ≤ 2` is the side condition `1 ≤ q` for `q = 2`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (G : Prop) (k : Integrable f μ → G) : G := by
  have hi : Integrable f μ := hf.integrable one_le_two
  exact k hi

/-! ### R2. `MemLp.integrable_sq` · context gains `Integrable (fun x => f x ^ 2) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (G : Prop)
    (k : Integrable (fun x => f x ^ 2) μ → G) : G := by
  have hs : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  exact k hs

/-! ### R3. `Integrable.const_mul` · context gains `Integrable (fun x => a * f x) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (a : ℝ)
    (G : Prop) (k : Integrable (fun x => a * f x) μ → G) : G := by
  have ha : Integrable (fun x => a * f x) μ := hf.const_mul a
  exact k ha

/-! ### R4. `Integrable.sub` · context gains `Integrable (f - g) μ`; state the type to get the `fun` form
Without a type, `hf.sub hg` has type `Integrable (f - g) μ`. Writing the type
`Integrable (fun x => f x - g x) μ` gives the same fact in the form `integral_add`/`integral_sub`
look for (R10, R11). `Integrable.add` is the same for `+`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (G : Prop) (k : Integrable (fun x => f x - g x) μ → G) : G := by
  have h₀ := hf.sub hg
  have h₁ : Integrable (fun x => f x - g x) μ := hf.sub hg
  exact k h₁

/-! ### R5. `integrable_const` · context gains `Integrable (fun x => c) μ` (finite measure) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) (G : Prop)
    (k : Integrable (fun _ : Ω => c) μ → G) : G := by
  have hc : Integrable (fun _ : Ω => c) μ := integrable_const c
  exact k hc

/-! ## Rewriting the integrand -/

/-! ### R6. `funext x` · goal: an equation of functions → the equation at a fresh point `x` -/
example {Ω : Type} (f : Ω → ℝ) (a : ℝ) :
    (fun x => (f x + a) * (f x - a)) = fun x => f x ^ 2 - a ^ 2 := by
  funext x
  ring

/-! ### R7. `ring` · closes an identity of commutative rings; `f x`, `∫ …`, `Var[…]` are unknowns -/
example (u v : ℝ) : (u + v) ^ 2 - 2 * u * v = u ^ 2 + v ^ 2 := by
  ring

/-! ## Variance and the integral rules -/

/-! ### R8. `variance_eq_sub` · goal: `Var[f; μ]` → `E[f²] - (E f)²`
`variance_eq_sub : MemLp f 2 μ → Var[f; μ] = ∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2`
(probability measure). `f ^ 2` is the function `x ↦ f x ^ 2`, applied to `x`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (P : ℝ → Prop) (h : P (∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2)) :
    P (Var[f; μ]) := by
  rw [variance_eq_sub hf]
  exact h

/-! ### R9. `rw [e]` with `e : (fun ω => …) = fun ω => …` · goal: the integrand is replaced
`μ[fun ω => F ω]` is displayed as `∫ (x : Ω), (fun ω => F ω) x ∂μ`: the function, applied to `x`.
`rw [e]` replaces that function and removes the application (beta reduction). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (a : ℝ) (P : ℝ → Prop)
    (e : (fun ω => (f ω + a) * (f ω - a)) = fun ω => f ω ^ 2 - a ^ 2)
    (h : P (∫ ω, f ω ^ 2 - a ^ 2 ∂μ)) : P μ[fun ω => (f ω + a) * (f ω - a)] := by
  rw [e]
  exact h

/-! ### R10. `integral_add` · goal: `∫ (f + g)` → `∫ f + ∫ g`
`integral_add : Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ x, f x ∂μ + ∫ x, g x ∂μ)) :
    P (∫ x, f x + g x ∂μ) := by
  rw [integral_add hf hg]
  exact h

/-! ### R11. `integral_sub` · goal: `∫ (f - g)` → `∫ f - ∫ g` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ x, f x ∂μ - ∫ x, g x ∂μ)) :
    P (∫ x, f x - g x ∂μ) := by
  rw [integral_sub hf hg]
  exact h

/-! ### R12. `integral_const_mul` · goal: `∫ r * f` → `r * ∫ f` (no integrability needed) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (r : ℝ) (P : ℝ → Prop)
    (h : P (r * ∫ x, f x ∂μ)) : P (∫ x, r * f x ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! ### R13. `Pi.pow_apply` · goal: `(f ^ n) x` → `f x ^ n`, also under `∫` (use `simp only`)
`rw` cannot rewrite under the binder `x` of `∫ x, …`; `simp only` can. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (P : ℝ → Prop)
    (h : P (∫ x, f x ^ 2 ∂μ)) : P (∫ x, (f ^ 2) x ∂μ) := by
  simp only [Pi.pow_apply]
  exact h

/-! ### R14. `integral_const` · goal: `∫ x, c ∂μ` → `μ.real Set.univ • c` (total mass times `c`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (P : ℝ → Prop)
    (h : P (μ.real Set.univ • c)) : P (∫ _ : Ω, c ∂μ) := by
  rw [integral_const]
  exact h

/-! ### R15. `probReal_univ` · goal: `μ.real Set.univ` → `1` for a probability measure -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ℝ → Prop)
    (h : P 1) : P (μ.real Set.univ) := by
  rw [probReal_univ]
  exact h

/-! ### R16. `smul_eq_mul`, `one_mul` · goal: `1 • c` → `1 * c` → `c` -/
example (c : ℝ) (P : ℝ → Prop) (h : P c) : P ((1 : ℝ) • c) := by
  rw [smul_eq_mul]
  rw [one_mul]
  exact h

/-! ## Using the first theorem in the second -/

/-! ### R17. `rw [T]` with `T : ∀ k, F k = G k` · goal: the FIRST `F _` found → `G _`
The open argument `k` is fixed at the first match, so a second `F _` needs a second `rw [T]`. -/
example (F G : ℝ → ℝ) (T : ∀ k, F k = G k) (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P (G a) (G b)) :
    P (F a) (F b) := by
  rw [T]
  rw [T]
  exact h

/-! ### R18. `sq_nonneg` · `sq_nonneg t : 0 ≤ t ^ 2` · context gains it -/
example (s t : ℝ) (G : Prop) (k : 0 ≤ (s - t) ^ 2 → G) : G := by
  have hst := sq_nonneg (s - t)
  exact k hst

/-! ### R19. `nlinarith [t₁, …]` · closes a real (in)equality that follows from the hints after
expanding with `ring` and multiplying pairs of hypotheses. -/
example (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `E[3 f + 2] = 3 E f + 2`: R3, R5, R10, R12, R14, R15, R16 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) : ∫ x, (3 * f x + 2) ∂μ = 3 * ∫ x, f x ∂μ + 2 := by
  have h3 : Integrable (fun x => 3 * f x) μ := hf.const_mul 3
  rw [integral_add h3 (integrable_const _)]
  rw [integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-! ### W2. `Var[f; μ] ≤ E[f²]`: R8, R13, R18, R19 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) : Var[f; μ] ≤ ∫ x, f x ^ 2 ∂μ := by
  rw [variance_eq_sub hf]
  simp only [Pi.pow_apply]
  nlinarith [sq_nonneg (∫ x, f x ∂μ)]

end M089Guide

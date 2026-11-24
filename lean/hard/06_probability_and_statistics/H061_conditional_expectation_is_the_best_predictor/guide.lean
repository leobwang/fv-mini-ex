/- Guide for H061 (Conditional expectation is the best predictor).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became, and
`G : Prop` with `h : T → G` is a goal the entry does not touch (the step only adds the fact `T`).
Part W: worked combinations on statements that are NOT the exercise's (linearity of a three-term
integral, the error `X - E[X | m]` has mean zero, the final inequality on plain numbers).
Assumed: Lean basics (E001–E033). Mathlib's measure theory is explained entry by entry.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H061Guide

/-! # Part R · Reference entries -/

/-! ## L² facts: integrability of products and of the conditional expectation -/

/-! ### R1. `MemLp.condExp` · context gains `MemLp μ[f | m] 2 μ`
Conditional expectation does not leave L²: `hf.condExp one_le_two` (the `1 ≤ p` argument, here `1 ≤ 2`). -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ)
    (G : Prop) (h : MemLp (μ[f | m]) 2 μ → G) : G := by
  have hc : MemLp (μ[f | m]) 2 μ := hf.condExp one_le_two
  exact h hc

/-! ### R2. `MemLp.integrable_mul` · context gains `Integrable (f * g) μ` (Hölder: L² · L² ⊆ L¹) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (G : Prop) (h : Integrable (f * g) μ → G) : G := by
  have hfg : Integrable (f * g) μ := hf.integrable_mul hg
  exact h hfg

/-! ### R3. `MemLp.integrable` · context gains `Integrable f μ` (L² ⊆ L¹ on a finite measure)
`hf.integrable one_le_two` uses `1 ≤ 2`; a probability measure is finite. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) [IsProbabilityMeasure μ]
    (hf : MemLp f 2 μ) (G : Prop) (h : Integrable f μ → G) : G := by
  have hi : Integrable f μ := hf.integrable one_le_two
  exact h hi

/-! ## Tower property and pulling out what is known -/

/-! ### R4. `integral_condExp` · `∫ μ[F | m] = ∫ F` (tower property: E[E[F | m]] = E[F])
Used right to left with the function named: `rw [← integral_condExp hm (f := F)]`. Without `(f := F)`
`rw` does not know which integral to wrap. -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω) (F : Ω → ℝ)
    [IsProbabilityMeasure μ] (P : ℝ → Prop) (h : P (∫ ω, (μ[F | m]) ω ∂μ)) :
    P (∫ ω, F ω ∂μ) := by
  rw [← integral_condExp hm (f := F)]
  exact h

/-! ### R5. `condExp_mul_of_stronglyMeasurable_left` · context gains `μ[f * g | m] =ᵐ[μ] f * μ[g | m]`
"Take out what is known": an `m`-measurable factor `f` leaves the conditional expectation. Needs
`StronglyMeasurable[m] f`, `Integrable (f * g) μ`, `Integrable g μ`. -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (μ : Measure Ω) (f g : Ω → ℝ)
    (hfm : StronglyMeasurable[m] f) (hfg : Integrable (f * g) μ) (hg : Integrable g μ)
    (G : Prop) (h : μ[f * g | m] =ᵐ[μ] f * μ[g | m] → G) : G := by
  have hp : μ[f * g | m] =ᵐ[μ] f * μ[g | m] := condExp_mul_of_stronglyMeasurable_left hfm hfg hg
  exact h hp

/-! ### R6. `integral_congr_ae` · goal `∫ f = ∫ g` → `f =ᵐ[μ] g` (equal almost everywhere) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (h : f =ᵐ[μ] g) :
    ∫ ω, f ω ∂μ = ∫ ω, g ω ∂μ := by
  apply integral_congr_ae
  exact h

/-! ## Rewriting the integrand -/

/-! ### R7. `funext ω` · goal: an equation of functions → the equation at one point `ω` -/
example {Ω : Type} (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) : (fun ω => f ω) = fun ω => g ω := by
  funext ω
  exact h ω

/-! ### R8. `Pi.mul_apply` · goal: `(f * g) ω` (product of functions, evaluated) → `f ω * g ω` -/
example {Ω : Type} (f g : Ω → ℝ) (ω : Ω) (P : ℝ → Prop) (h : P (f ω * g ω)) : P ((f * g) ω) := by
  simp only [Pi.mul_apply]
  exact h

/-! ### R9. `integral_sub` · goal: `∫ (f - g)` → `∫ f - ∫ g`; needs both integrable -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ ω, f ω ∂μ - ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω - g ω ∂μ) := by
  rw [integral_sub hf hg]
  exact h

/-! ### R10. `sub_self` · goal: `a - a` → `0` -/
example (a : ℝ) (P : ℝ → Prop) (h : P 0) : P (a - a) := by
  rw [sub_self]
  exact h

/-! ## Integrability of the expansion, in lambda form -/

/-! ### R11. `MemLp.sub` · context gains `MemLp (f - g) 2 μ` (L² is closed under `-`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (G : Prop) (h : MemLp (f - g) 2 μ → G) : G := by
  have hd : MemLp (f - g) 2 μ := hf.sub hg
  exact h hd

/-! ### R12. `MemLp.integrable_sq` · context gains `Integrable (fun ω => f ω ^ 2) μ`
Applied to `hd : MemLp (f - g) 2 μ` it may be stated as `Integrable (fun ω => (f ω - g ω) ^ 2) μ`:
`(f - g) ω` and `f ω - g ω` are equal by definition, so `have` accepts either form. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hd : MemLp (f - g) 2 μ)
    (G : Prop) (h : Integrable (fun ω => (f ω - g ω) ^ 2) μ → G) : G := by
  have hs : Integrable (fun ω => (f ω - g ω) ^ 2) μ := hd.integrable_sq
  exact h hs

/-! ### R13. `Integrable.const_mul` · context gains `Integrable (fun ω => c * f ω) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)
    (G : Prop) (h : Integrable (fun ω => c * f ω) μ → G) : G := by
  have hc : Integrable (fun ω => c * f ω) μ := hf.const_mul c
  exact h hc

/-! ### R14. `Integrable.add` · context gains `Integrable (fun ω => f ω + g ω) μ`
The lemma's own result is `Integrable (f + g) μ`; the `have` restates it in lambda form. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (G : Prop) (h : Integrable (fun ω => f ω + g ω) μ → G) : G := by
  have hs : Integrable (fun ω => f ω + g ω) μ := hf.add hg
  exact h hs

/-! ## Expanding the square under the integral -/

/-! ### R15. `calc` · goal `a = c` → one goal per step (`a = b`, then `b = c`)
`_ = _ := by …` as the last step lets Lean fill in the right side `c` from the goal. -/
example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := ?_
    _ = _ := ?_
  exact h1
  exact h2

/-! ### R16. `congr 1` · goal `∫ ω, F ω ∂μ = ∫ ω, H ω ∂μ` → the integrands are equal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) :
    ∫ ω, f ω + g ω ∂μ = ∫ ω, g ω + f ω ∂μ := by
  congr 1
  funext ω
  exact add_comm (f ω) (g ω)

/-! ### R17. `integral_add` · goal: `∫ (f + g)` → `∫ f + ∫ g`; needs both integrable, in lambda form
When the summands are compound (`(f ω - g ω) ^ 2`), `hf` must be stated as
`Integrable (fun ω => …) μ` with exactly the summand of the goal (R12–R14), or `rw` finds no match. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Integrable (fun ω => f ω ^ 2) μ) (hg : Integrable (fun ω => 2 * g ω) μ) (P : ℝ → Prop)
    (h : P (∫ ω, f ω ^ 2 ∂μ + ∫ ω, 2 * g ω ∂μ)) :
    P (∫ ω, f ω ^ 2 + 2 * g ω ∂μ) := by
  rw [integral_add hf hg]
  exact h

/-! ### R18. `integral_const_mul` · goal: `∫ ω, c * f ω ∂μ` → `c * ∫ ω, f ω ∂μ` (no hypotheses) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) (P : ℝ → Prop)
    (h : P (c * ∫ ω, f ω ∂μ)) : P (∫ ω, c * f ω ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! ## The main theorem: measurability, nonnegativity, linear arithmetic -/

/-! ### R19. `stronglyMeasurable_condExp` · context gains `StronglyMeasurable[m] μ[f | m]`
`E[f | m]` is `m`-measurable by construction. Write the type with `[m]`: the infoview hides it. -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (μ : Measure Ω) (f : Ω → ℝ) (G : Prop)
    (h : StronglyMeasurable[m] (μ[f | m]) → G) : G := by
  have hc : StronglyMeasurable[m] (μ[f | m]) := stronglyMeasurable_condExp
  exact h hc

/-! ### R20. `StronglyMeasurable.sub` · context gains `StronglyMeasurable[m] (f - g)` -/
example {Ω : Type} {m : MeasurableSpace Ω} (f g : Ω → ℝ) (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (G : Prop) (h : StronglyMeasurable[m] (f - g) → G) : G := by
  have hd : StronglyMeasurable[m] (f - g) := hf.sub hg
  exact h hd

/-! ### R21. `mul_zero`, `add_zero` · goal: `a * 0` → `0`, then `a + 0` → `a` -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a + c)) : P (a + b * 0 + c) := by
  rw [mul_zero]
  rw [add_zero]
  exact h

/-! ### R22. `integral_nonneg` · goal `0 ≤ ∫ f` → `0 ≤ f` (pointwise: `∀ ω, 0 ≤ f ω`)
`intro ω` then opens the pointwise goal; a term `fun ω => …` proves it directly. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω ^ 2) :
    0 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  apply integral_nonneg
  intro ω
  exact h ω

/-! ### R23. `sq_nonneg` · closes `0 ≤ a ^ 2` -/
example (a : ℝ) : 0 ≤ a ^ 2 := sq_nonneg a

/-! ### R24. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (a b c : ℝ) (h : a = b + c) (hc : 0 ≤ c) : b ≤ a := by
  linarith

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. A three-term integral split by linearity: R13, R14, R17, R18 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g k : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hk : Integrable k μ) :
    ∫ ω, f ω + g ω + 3 * k ω ∂μ = ∫ ω, f ω ∂μ + ∫ ω, g ω ∂μ + 3 * ∫ ω, k ω ∂μ := by
  have hfg : Integrable (fun ω => f ω + g ω) μ := hf.add hg
  have hk3 : Integrable (fun ω => 3 * k ω) μ := hk.const_mul 3
  rw [integral_add hfg hk3, integral_add hf hg, integral_const_mul]

/-! ### W2. The error `X - E[X | m]` has mean zero: R1, R3, R9, R4, R10 -/
example {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω) (X : Ω → ℝ)
    [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) :
    ∫ ω, X ω - (μ[X | m]) ω ∂μ = 0 := by
  have hZ : Integrable (μ[X | m]) μ := (hX.condExp one_le_two).integrable one_le_two
  rw [integral_sub (hX.integrable one_le_two) hZ]
  rw [integral_condExp hm]
  rw [sub_self]

/-! ### W3. Drop a zero middle term, then compare: R21, R22 → R23, R24 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (a b : ℝ)
    (hs : a = b + 2 * 0 + ∫ ω, f ω ^ 2 ∂μ) : b ≤ a := by
  rw [mul_zero, add_zero] at hs
  have hn : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg (f ω)
  linarith

end H061Guide

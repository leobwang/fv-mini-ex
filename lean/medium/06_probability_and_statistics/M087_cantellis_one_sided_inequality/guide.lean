/- Guide for M087 (Cantelli's one-sided inequality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` with `h : T → G` is a goal the entry does not touch; `h` shows which fact `T` was added.
Part W: worked combinations on statements that are NOT the exercise's (Markov on `f²`, a centred
mean, a different optimisation).
Assumed: Lean basics (E001–E033). Mathlib's measure theory is explained entry by entry.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M087Guide

/-! # Part R · Reference entries -/

/-! ## Naming terms and integrability facts -/

/-! ### R1. `obtain ⟨m, hm⟩ : ∃ m, e = m := ⟨_, rfl⟩` · context gains a name `m` for the term `e`
The goal still shows `e`; `rw [hm]` then replaces it by `m`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (P : ℝ → Prop)
    (h : P μ[f]) : P μ[f] := by
  obtain ⟨m, hm⟩ : ∃ m, μ[f] = m := ⟨_, rfl⟩
  exact h

/-! ### R2. `MemLp.integrable` · context gains `Integrable f μ` (from a finite second moment)
`hf.integrable one_le_two` uses `1 ≤ 2`: an L² function on a finite measure is L¹. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (G : Prop) (h : Integrable f μ → G) : G := by
  have hi : Integrable f μ := hf.integrable one_le_two
  exact h hi

/-! ### R3. `MemLp.aemeasurable` · context gains `AEMeasurable f μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (G : Prop)
    (h : AEMeasurable f μ → G) : G := by
  have hm := hf.aemeasurable
  exact h hm

/-! ### R4. `variance_eq_integral` · goal: `Var[f; μ]` → `∫ ω, (f ω - E f) ^ 2 ∂μ` (needs `AEMeasurable f μ`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (P : ℝ → Prop) (h : P (∫ ω, (f ω - μ[f]) ^ 2 ∂μ)) : P Var[f; μ] := by
  rw [variance_eq_integral hf]
  exact h

/-! ### R5. `memLp_const`, `MemLp.sub` · context gains `MemLp (f - fun x => c) 2 μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (c : ℝ) (G : Prop) (h : MemLp (f - fun _ => c) 2 μ → G) : G := by
  have hs := hf.sub (memLp_const c)
  exact h hs

/-! ### R6. `MemLp.integrable_sq` · context gains `Integrable (fun ω => g ω ^ 2) μ`
Here `g = f - fun _ => c`; the stated type puts it in the lambda form `(f ω - c) ^ 2`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ)
    (hs : MemLp (f - fun _ => c) 2 μ) (G : Prop) (h : Integrable (fun ω => (f ω - c) ^ 2) μ → G) :
    G := by
  have h2 : Integrable (fun ω => (f ω - c) ^ 2) μ := hs.integrable_sq
  exact h h2

/-! ### R7. `integrable_const` · context gains `Integrable (fun x => c) μ` (finite measure) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) (G : Prop)
    (h : Integrable (fun _ : Ω => c) μ → G) : G := by
  have hc := integrable_const (μ := μ) c
  exact h hc

/-! ### R8. `Integrable.sub` (and `Integrable.add`) · context gains `Integrable (fun ω => f ω - g ω) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (G : Prop) (h : Integrable (fun ω => f ω - g ω) μ → G) : G := by
  have hs : Integrable (fun ω => f ω - g ω) μ := hf.sub hg
  exact h hs

/-! ### R9. `Integrable.const_mul` · context gains `Integrable (fun ω => c * f ω) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)
    (G : Prop) (h : Integrable (fun ω => c * f ω) μ → G) : G := by
  have hc := hf.const_mul c
  exact h hc

/-! ## Computing integrals -/

/-! ### R10. `integral_add` · goal: `∫ (f + g)` → `∫ f + ∫ g`, given `Integrable f μ`, `Integrable g μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ ω, f ω ∂μ + ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω + g ω ∂μ) := by
  rw [integral_add hf hg]
  exact h

/-! ### R11. `integral_const_mul` · goal: `∫ ω, c * f ω ∂μ` → `c * ∫ ω, f ω ∂μ` (no side goal) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) (P : ℝ → Prop)
    (h : P (c * ∫ ω, f ω ∂μ)) : P (∫ ω, c * f ω ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! ### R12. `integral_sub` · goal: `∫ (f - g)` → `∫ f - ∫ g`, given `Integrable f μ`, `Integrable g μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ ω, f ω ∂μ - ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω - g ω ∂μ) := by
  rw [integral_sub hf hg]
  exact h

/-! ### R13. `simp` on `∫ ω, c ∂μ` · goal: the integral of a constant → the constant (probability measure) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ)
    (P : ℝ → Prop) (h : P c) : P (∫ _ω, c ∂μ) := by
  simp
  exact h

/-! ## Markov's inequality and events -/

/-! ### R14. `mul_meas_ge_le_integral_of_nonneg` (Markov) · context gains `ε * P(ε ≤ f) ≤ E f`
Arguments: `0 ≤ᵐ[μ] f` (R15), `Integrable f μ`, and the level `ε : ℝ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hnn : 0 ≤ᵐ[μ] f)
    (hfi : Integrable f μ) (ε : ℝ) (G : Prop)
    (h : ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ → G) : G := by
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn hfi ε
  exact h hmk

/-! ### R15. `Filter.Eventually.of_forall` · goal `0 ≤ᵐ[μ] f` (a.e.) → `∀ x, 0 x ≤ f x` (everywhere)
`0 x` is the zero function applied to `x`, i.e. the number `0`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ᵐ[μ] f := by
  apply Filter.Eventually.of_forall
  exact h

/-! ### R16. `sq_nonneg` · context gains `0 ≤ a ^ 2` -/
example (a : ℝ) (G : Prop) (h : 0 ≤ a ^ 2 → G) : G := by
  have hsq := sq_nonneg a
  exact h hsq

/-! ### R17. `nlinarith [t₁, …]` · closes a goal that needs products of hypotheses and the hints `tᵢ` -/
example (x y : ℝ) : 0 ≤ x ^ 2 - 2 * x * y + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-! ### R18. `rw [e] at h ⊢` · context and goal: rewrite a hypothesis `h` (and, with `⊢`, the goal) -/
example (a b : ℝ) (e : a = b) (P Q : ℝ → Prop) (h : P a) (k : P b → Q b) : Q a := by
  rw [e] at h ⊢
  exact k h

/-! ### R19. `intro ω hω` on `s ⊆ t` · goal: inclusion → membership; context gains `ω`, `hω : ω ∈ s` -/
example {Ω : Type} (s t : Set Ω) (h : ∀ ω, ω ∈ s → ω ∈ t) : s ⊆ t := by
  intro ω hω
  exact h ω hω

/-! ### R20. `simp only [Set.mem_setOf_eq] at hω ⊢` · context and goal: `ω ∈ {x | Q x}` → `Q ω` -/
example {Ω : Type} (Q R : Ω → Prop) (ω : Ω) (hω : ω ∈ {x | Q x}) (h : Q ω → R ω) :
    ω ∈ {x | R x} := by
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact h hω

/-! ### R21. `measureReal_mono` · context gains `μ.real s ≤ μ.real t` from `s ⊆ t` (finite measure)
`μ` is not visible in `s ⊆ t`, so name it: `measureReal_mono (μ := μ) hst`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Set Ω)
    (hst : s ⊆ t) (G : Prop) (h : μ.real s ≤ μ.real t → G) : G := by
  have hle := measureReal_mono (μ := μ) hst
  exact h hle

/-! ## Facts about the variance and the final algebra -/

/-! ### R22. `variance_nonneg` · context gains `0 ≤ Var[f; μ]` (no hypotheses needed) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (G : Prop)
    (h : 0 ≤ Var[f; μ] → G) : G := by
  have hv := variance_nonneg f μ
  exact h hv

/-! ### R23. `LT.lt.le` · context gains `0 ≤ t` from `ht : 0 < t` (written `ht.le`) -/
example (t : ℝ) (ht : 0 < t) (G : Prop) (h : 0 ≤ t → G) : G := by
  have ht' := ht.le
  exact h ht'

/-! ### R24. `div_nonneg` · goal `0 ≤ a / b` → `0 ≤ a`, `0 ≤ b` -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  apply div_nonneg
  exact ha
  exact hb

/-! ### R25. `e ▸ t` · context gains `t` with `a` replaced by `b`, from `e : a = b` and `t : 0 ≤ a` -/
example (a b : ℝ) (e : a = b) (ha : 0 ≤ a) (G : Prop) (h : 0 ≤ b → G) : G := by
  have hb : 0 ≤ b := e ▸ ha
  exact h hb

/-! ### R26. `field_simp` · goal: multiply out the denominators (needs them `≠ 0`; `0 < a` in context will do) -/
example (a b : ℝ) (ha : 0 < a) : (a + b / a) * 2 = (2 * b + 2 * a ^ 2) / a := by
  field_simp
  ring

/-! ### R27. `mul_div_assoc'` · `a * (b / c) = a * b / c` -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * b / c)) : P (a * (b / c)) := by
  rw [mul_div_assoc']
  exact h

/-! ### R28. `div_le_div_iff_of_pos_right` · `0 < c → (a / c ≤ b / c ↔ a ≤ b)`: cancel a positive denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : a / c ≤ b / c) : a ≤ b := by
  rw [div_le_div_iff_of_pos_right hc] at h
  exact h

/-! ### R29. `positivity` · closes `0 < e` or `0 ≤ e` built from `+`, `*`, `^`, `/` and positive atoms -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < b + 2 * a ^ 2 := by
  positivity

/-! ### R30. `le_div_iff₀` · `0 < c → (a ≤ b / c ↔ a * c ≤ b)` · goal: clear the denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  rw [le_div_iff₀ hc]
  exact h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Markov on `f ^ 2` (a Chebyshev-type step): R6, R15, R16, R14 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (c : ℝ) :
    c * μ.real {x | c ≤ f x ^ 2} ≤ ∫ x, f x ^ 2 ∂μ := by
  have hi : Integrable (fun ω => f ω ^ 2) μ := hf.integrable_sq
  have hnn : 0 ≤ᵐ[μ] fun ω => f ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => show (0 : ℝ) ≤ f ω ^ 2 from sq_nonneg (f ω)
  exact mul_meas_ge_le_integral_of_nonneg hnn hi c

/-! ### W2. A centred variable has mean zero: R1, R2, R7, R12, then `rw [hm]` and R13 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) : ∫ ω, (f ω - μ[f]) ∂μ = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, μ[f] = m := ⟨_, rfl⟩
  have hfi : Integrable f μ := hf.integrable one_le_two
  rw [hm, integral_sub hfi (integrable_const m)]
  rw [hm]
  simp

/-! ### W3. Cancel a common positive denominator, then clear another: R27, R28, R29, R30, R17 -/
example (p a b : ℝ) (ha : 0 < a)
    (h : p * ((a + 1) ^ 2 / a ^ 2) ≤ b * (a + 1) / a ^ 2) : p ≤ b / (a + 1) := by
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end M087Guide

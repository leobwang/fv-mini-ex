/- Guide for M085 (Chebyshev from Markov).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` with `h : T → G` is a goal the entry does not touch; `h` shows which fact `T` was added.
Part W: worked combinations on statements that are NOT the exercise's (cubes instead of squares,
Markov on `f ²`, clearing a denominator).
Assumed: Lean basics (E001–E033). Mathlib's measure theory is explained entry by entry.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M085Guide

/-! # Part R · Reference entries -/

/-! ## Two descriptions of one event -/

/-! ### R1. `ext ω` on sets (lemma `Set.ext`) · goal `s = t` → context gains `ω`, goal `ω ∈ s ↔ ω ∈ t` -/
example {Ω : Type} (s t : Set Ω) (h : ∀ ω, ω ∈ s ↔ ω ∈ t) : s = t := by
  ext ω
  exact h ω

/-! ### R2. `simp only [Set.mem_setOf_eq]` · goal: `ω ∈ {x | p x}` → `p ω` -/
example {Ω : Type} (p q : Ω → Prop) (ω : Ω) (h : p ω ↔ q ω) :
    ω ∈ {x | p x} ↔ ω ∈ {x | q x} := by
  simp only [Set.mem_setOf_eq]
  exact h

/-! ### R3. `sq_abs` · `|a| ^ 2 = a ^ 2`; right to left, `rw [← sq_abs a]` turns `a ^ 2` into `|a| ^ 2`
Give the argument `a`: without it `rw [← sq_abs]` does not know which square to rewrite. -/
example (a : ℝ) (P : ℝ → Prop) (h : P (|a| ^ 2)) : P (a ^ 2) := by
  rw [← sq_abs a]
  exact h

/-! ### R4. `abs_nonneg` · context gains `0 ≤ |a|` -/
example (a : ℝ) (G : Prop) (h : 0 ≤ |a| → G) : G := by
  have ha := abs_nonneg a
  exact h ha

/-! ### R5. `LT.lt.le` · context gains `0 ≤ c` from `hc : 0 < c` (written `hc.le`) -/
example (c : ℝ) (hc : 0 < c) (G : Prop) (h : 0 ≤ c → G) : G := by
  have hc' := hc.le
  exact h hc'

/-! ### R6. `two_ne_zero` · context gains `2 ≠ 0` (here in `ℕ`, the type of exponents) -/
example (G : Prop) (h : (2 : ℕ) ≠ 0 → G) : G := by
  have h2 : (2 : ℕ) ≠ 0 := two_ne_zero
  exact h h2

/-! ### R7. `pow_le_pow_iff_left₀` · `0 ≤ a → 0 ≤ b → n ≠ 0 → (a ^ n ≤ b ^ n ↔ a ≤ b)` · context -/
example (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) (G : Prop)
    (h : (a ^ n ≤ b ^ n ↔ a ≤ b) → G) : G := by
  have hiff := pow_le_pow_iff_left₀ ha hb hn
  exact h hiff

/-! ### R8. `Iff.symm` · `(A ↔ B) → (B ↔ A)`, written `h.symm` · closes the flipped `↔` -/
example (A B : Prop) (h : A ↔ B) : B ↔ A := by
  exact h.symm

/-! ## Integrability of the squared deviation -/

/-! ### R9. `memLp_const`, `MemLp.sub` · context gains `MemLp (f - fun x => c) 2 μ`
`memLp_const c : MemLp (fun _ => c) p μ` needs a finite measure; `MemLp.sub` subtracts two `MemLp` facts. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (c : ℝ) (G : Prop) (h : MemLp (f - fun _ => c) 2 μ → G) : G := by
  have hs := hf.sub (memLp_const c)
  exact h hs

/-! ### R10. `MemLp.integrable_sq` · context gains `Integrable (fun ω => g ω ^ 2) μ` from `MemLp g 2 μ`
Here `g = f - fun _ => c`; the stated type puts it in the lambda form `(f ω - c) ^ 2`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ)
    (hs : MemLp (f - fun _ => c) 2 μ) (G : Prop) (h : Integrable (fun ω => (f ω - c) ^ 2) μ → G) :
    G := by
  have h2 : Integrable (fun ω => (f ω - c) ^ 2) μ := hs.integrable_sq
  exact h h2

/-! ## Markov's inequality -/

/-! ### R11. `mul_meas_ge_le_integral_of_nonneg` (Markov) · context gains `ε * P(ε ≤ f) ≤ E f`
Arguments: `0 ≤ᵐ[μ] f` (R12), `Integrable f μ`, and the level `ε : ℝ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hnn : 0 ≤ᵐ[μ] f)
    (hfi : Integrable f μ) (ε : ℝ) (G : Prop)
    (h : ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ → G) : G := by
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn hfi ε
  exact h hmk

/-! ### R12. `Filter.Eventually.of_forall` · goal `0 ≤ᵐ[μ] f` (a.e.) → `∀ x, 0 x ≤ f x` (everywhere)
`0 x` is the zero function applied to `x`, i.e. the number `0`. As a term:
`Filter.Eventually.of_forall fun ω => (proof of 0 ≤ f ω)`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ᵐ[μ] f := by
  apply Filter.Eventually.of_forall
  exact h

/-! ### R13. `sq_nonneg` · context gains `0 ≤ a ^ 2` -/
example (a : ℝ) (G : Prop) (h : 0 ≤ a ^ 2 → G) : G := by
  have hsq := sq_nonneg a
  exact h hsq

/-! ## From the integral to the variance -/

/-! ### R14. `MemLp.aemeasurable` · context gains `AEMeasurable f μ` (written `hf.aemeasurable`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (G : Prop)
    (h : AEMeasurable f μ → G) : G := by
  have hm := hf.aemeasurable
  exact h hm

/-! ### R15. `variance_eq_integral` · `AEMeasurable f μ → Var[f; μ] = ∫ ω, (f ω - μ[f]) ^ 2 ∂μ`
Right to left, `rw [← variance_eq_integral hf]` folds the integral back into `Var[f; μ]`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : AEMeasurable f μ)
    (P : ℝ → Prop) (h : P Var[f; μ]) : P (∫ ω, (f ω - μ[f]) ^ 2 ∂μ) := by
  rw [← variance_eq_integral hf]
  exact h

/-! ### R16. `rw [← e] at h` · context: in hypothesis `h`, every `b` → `a`, from `e : a = b`
The goal is untouched. Works for any type, sets included. -/
example {α : Type} (a b : α) (e : a = b) (P : α → Prop) (Q : Prop) (h : P b) (k : P a → Q) :
    Q := by
  rw [← e] at h
  exact k h

/-! ## The final inequality -/

/-! ### R17. `le_div_iff₀` · `0 < c → (a ≤ b / c ↔ a * c ≤ b)` · goal: clear the denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  rw [le_div_iff₀ hc]
  exact h

/-! ### R18. `positivity` · closes `0 < e` or `0 ≤ e` built from `+`, `*`, `^`, `/` and positive atoms -/
example (c : ℝ) (hc : 0 < c) : 0 < c ^ 2 := by
  positivity

/-! ### R19. `linarith` · closes a linear goal from the hypotheses; a product such as `k * p` counts as
one unknown, and `k * p` and `p * k` are the same unknown -/
example (p k v : ℝ) (h : k * p ≤ v) : p * k ≤ v := by
  linarith

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. The same event, described by cubes (nonnegative `f`): R1, R2, R7, R8 -/
example {Ω : Type} (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (c : ℝ) (hc : 0 ≤ c) :
    {ω | c ≤ f ω} = {ω | c ^ 3 ≤ f ω ^ 3} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  exact (pow_le_pow_iff_left₀ hc (hf ω) (by norm_num)).symm

/-! ### W2. Markov on `f ^ 2`: R10, R12 with R13, R11 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (c : ℝ) :
    c * μ.real {x | c ≤ f x ^ 2} ≤ ∫ x, f x ^ 2 ∂μ := by
  have hi : Integrable (fun ω => f ω ^ 2) μ := hf.integrable_sq
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω)) hi c
  exact hmk

/-! ### W3. From `k * p ≤ v` to `p ≤ v / k`: R17 with R18, then R19 -/
example (p v a : ℝ) (ha : 0 < a) (h : (a + 1) ^ 3 * p ≤ v) : p ≤ v / (a + 1) ^ 3 := by
  rw [le_div_iff₀ (by positivity)]
  linarith

end M085Guide

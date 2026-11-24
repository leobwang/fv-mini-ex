/- Guide for M093 (Jensen off a closed domain: E[1/X] ≥ 1/E[X]).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` with `k : T → G` is a goal the entry does not touch; `k` shows which fact `T` was added.
Part W: worked combinations on statements that are NOT the exercise's (`exp f > 0`, a line `3 - f/2`,
the bound `3/x - 2/x² ≤ 9/8`).
Assumed: Lean basics (E001–E033). Mathlib's measure theory is explained entry by entry.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M093Guide

/-! # Part R · Reference entries -/

/-! ## A positive integrand has a positive integral -/

/-! ### R1. `integral_pos_iff_support_of_nonneg` · goal: `0 < ∫ f` → `0 < μ (support f)`
`0 ≤ f → Integrable f μ → (0 < ∫ x, f x ∂μ ↔ 0 < μ (Function.support f))`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : 0 ≤ f)
    (hi : Integrable f μ) (h : 0 < μ (Function.support f)) : 0 < ∫ ω, f ω ∂μ := by
  rw [integral_pos_iff_support_of_nonneg hf hi]
  exact h

/-! ### R2. `fun ω => (h ω).le` (`LT.lt.le`) · context gains `0 ≤ f` from `∀ ω, 0 < f ω`
`0 ≤ f` on functions means `∀ ω, 0 ≤ f ω`; `(h ω).le` turns `0 < f ω` into `0 ≤ f ω`. -/
example {Ω : Type} (f : Ω → ℝ) (h : ∀ ω, 0 < f ω) (G : Prop) (k : 0 ≤ f → G) : G := by
  have hf : 0 ≤ f := fun ω => (h ω).le
  exact k hf

/-! ### R3. `ext ω` on sets (`Set.ext`) · goal `s = t` → `ω ∈ s ↔ ω ∈ t`; context gains `ω` -/
example {Ω : Type} (s t : Set Ω) (h : ∀ ω, ω ∈ s ↔ ω ∈ t) : s = t := by
  ext ω
  exact h ω

/-! ### R4. `Function.mem_support`, `Set.mem_univ` · goal: `ω ∈ support f ↔ ω ∈ univ` → `f ω ≠ 0`
`Function.mem_support : x ∈ Function.support f ↔ f x ≠ 0`; `Set.mem_univ : x ∈ Set.univ` is `True`. -/
example {Ω : Type} (f : Ω → ℝ) (ω : Ω) (h : f ω ≠ 0) :
    ω ∈ Function.support f ↔ ω ∈ Set.univ := by
  simp only [Function.mem_support, Set.mem_univ, iff_true]
  exact h

/-! ### R5. `LT.lt.ne'` · context gains `a ≠ 0` from `ha : 0 < a` (written `ha.ne'`) -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (k : a ≠ 0 → G) : G := by
  have hne := ha.ne'
  exact k hne

/-! ### R6. `measure_univ` · goal: `μ Set.univ` → `1` (probability measure)
`μ s` lives in `ℝ≥0∞` (`[0, ∞]`); `0 < 1` there is `zero_lt_one`. `simp` does all of this by itself. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    0 < μ Set.univ := by
  rw [measure_univ]
  exact zero_lt_one

/-! ## Naming the mean -/

/-! ### R7. `set m := e` · context gains `m : ℝ := e`; every `e` in goal and context → `m` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (h0 : 0 < μ[f])
    (P : ℝ → Prop) (h : ∀ m, 0 < m → P m) : P μ[f] := by
  set m := μ[f]
  exact h m h0

/-! ## Clearing denominators in a real inequality -/

/-! ### R8. `div_sub_div` · `b ≠ 0 → d ≠ 0 → a / b - c / d = (a * d - b * c) / (b * d)`
Arguments: `div_sub_div a c hb hd` (or `div_sub_div _ _ hb hd`). -/
example (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) (P : ℝ → Prop)
    (h : P ((a * d - b * c) / (b * d))) : P (a / b - c / d) := by
  rw [div_sub_div a c hb hd]
  exact h

/-! ### R9. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` built from `+`, `*`, `^`, `/` and positive atoms -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a * b ^ 2 ≠ 0 := by
  positivity

/-! ### R10. `div_le_iff₀` · `0 < c → (b / c ≤ a ↔ b ≤ a * c)` · goal: clear the denominator on the left -/
example (a b c : ℝ) (hc : 0 < c) (h : b ≤ a * c) : b / c ≤ a := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R11. `field_simp` · goal: multiply out every denominator it can prove `≠ 0`
It reads `0 < a` (or `a ≠ 0`) from the context. Its output shape is not predictable: look at it. -/
example (a b c : ℝ) (ha : 0 < a) (h : c * a ≤ b) : c ≤ a⁻¹ * b := by
  field_simp
  exact h

/-! ### R12. `sq_nonneg` · context gains `0 ≤ a ^ 2` -/
example (a : ℝ) (G : Prop) (k : 0 ≤ a ^ 2 → G) : G := by
  have hsq := sq_nonneg a
  exact k hsq

/-! ### R13. `nlinarith [t₁, …]` · closes a polynomial inequality using products of hypotheses and hints `tᵢ` -/
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ## Integrability facts -/

/-! ### R14. `integrable_const` · context gains `Integrable (fun x => c) μ` (finite measure) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) (G : Prop)
    (k : Integrable (fun _ : Ω => c) μ → G) : G := by
  have hc := integrable_const (μ := μ) c
  exact k hc

/-! ### R15. `Integrable.sub` · context gains `Integrable (fun ω => f ω - g ω) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (G : Prop) (k : Integrable (fun ω => f ω - g ω) μ → G) : G := by
  have hs : Integrable (fun ω => f ω - g ω) μ := hf.sub hg
  exact k hs

/-! ### R16. `Integrable.div_const` · context gains `Integrable (fun x => f x / c) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)
    (G : Prop) (k : Integrable (fun x => f x / c) μ → G) : G := by
  have hd := hf.div_const c
  exact k hd

/-! ## Computing and comparing integrals -/

/-! ### R17. `calc` · goal `a ≤ c` → one goal per step (`a = b`, then `b ≤ c`)
Each step is `_ rel rhs := proof`; `_` is the previous right-hand side. `?_` leaves a step as a goal. -/
example (a b c : ℝ) (h1 : a = b) (h2 : b ≤ c) : a ≤ c := by
  calc a = b := ?_
    _ ≤ c := ?_
  exact h1
  exact h2

/-! ### R18. `integral_div` · `∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r` · context gains it as `h2`
State it with `have` and the exact integrand you need: a bare `rw [integral_div]` rewrites the FIRST
integral of the form `∫ … / r`, which may be a constant `∫ c / r` (second example). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (r : ℝ) (G : Prop)
    (k : ∫ ω, f ω / r ∂μ = (∫ ω, f ω ∂μ) / r → G) : G := by
  have h2 : ∫ ω, f ω / r ∂μ = (∫ ω, f ω ∂μ) / r := integral_div r f
  exact k h2

example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c r : ℝ) (P : ℝ → Prop)
    (h : P ((∫ _a, c ∂μ) / r - ∫ ω, f ω / r ∂μ)) : P (∫ _ω, c / r ∂μ - ∫ ω, f ω / r ∂μ) := by
  rw [integral_div]
  exact h

/-! ### R19. `integral_sub` · goal: `∫ (f - g)` → `∫ f - ∫ g`, given `Integrable f μ`, `Integrable g μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ ω, f ω ∂μ - ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω - g ω ∂μ) := by
  rw [integral_sub hf hg]
  exact h

/-! ### R20. `integral_const` · goal: `∫ x, c ∂μ` → `μ.real Set.univ • c` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (P : ℝ → Prop)
    (h : P (μ.real Set.univ • c)) : P (∫ _ω, c ∂μ) := by
  rw [integral_const]
  exact h

/-! ### R21. `probReal_univ`, `one_smul` · goal: `μ.real Set.univ • c` → `1 • c` → `c` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ)
    (P : ℝ → Prop) (h : P c) : P (μ.real Set.univ • c) := by
  rw [probReal_univ]
  rw [one_smul]
  exact h

/-! ### R22. `integral_mono` · goal `∫ f ≤ ∫ g` → `f ≤ g` (pointwise), given both integrable
`Integrable f μ → Integrable g μ → f ≤ g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`; `f ≤ g` is `∀ ω, f ω ≤ g ω`.
When Lean reports `don't know how to synthesize implicit argument f`, name it: `integral_mono (f := fun ω => …)`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (h : ∀ ω, f ω ≤ g ω) : ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ := by
  refine integral_mono hf hg ?_
  exact h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. A strictly positive integrand has a positive mean: R1 with R2, R3, R4 with R5, R6 by `simp` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hi : Integrable (fun ω => Real.exp (f ω)) μ) : 0 < ∫ ω, Real.exp (f ω) ∂μ := by
  have hp : ∀ ω, 0 < Real.exp (f ω) := fun ω => Real.exp_pos (f ω)
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hp ω).le) hi]
  have hs : Function.support (fun ω => Real.exp (f ω)) = Set.univ := by
    ext ω
    simp [(hp ω).ne']
  simp [hs]

/-! ### W2. The mean of a line `3 - f / 2`: R18 (as a `have`), R19 with R14, R16, R20, R21 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) : ∫ ω, (3 - f ω / 2) ∂μ = 3 - (∫ ω, f ω ∂μ) / 2 := by
  have h2 : ∫ ω, f ω / 2 ∂μ = (∫ ω, f ω ∂μ) / 2 := integral_div 2 f
  rw [integral_sub (integrable_const _) (hf.div_const _)]
  rw [h2, integral_const]
  simp only [probReal_univ, one_smul]

/-! ### W3. `calc`: compute a mean, then integrate a pointwise bound naming `f`: R17, R19, R20, R21, R22 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hb : ∀ ω, f ω - 1 ≤ g ω) :
    ∫ ω, f ω ∂μ - 1 ≤ ∫ ω, g ω ∂μ := by
  calc ∫ ω, f ω ∂μ - 1 = ∫ ω, (f ω - 1) ∂μ := by
        rw [integral_sub hf (integrable_const _), integral_const]
        simp only [probReal_univ, one_smul]
    _ ≤ ∫ ω, g ω ∂μ := integral_mono (f := fun ω => f ω - 1) (hf.sub (integrable_const _)) hg hb

/-! ### W4. `3 / x - 2 / x² ≤ 9 / 8` for `x > 0`: R8 with R5, R9; R10 with R9; R13 with R12
Multiplied out it is `x (3x - 4)² ≥ 0`. -/
example (x : ℝ) (hx : 0 < x) : 3 / x - 2 / x ^ 2 ≤ 9 / 8 := by
  rw [div_sub_div _ _ hx.ne' (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hx.le (sq_nonneg (3 * x - 4))]

end M093Guide

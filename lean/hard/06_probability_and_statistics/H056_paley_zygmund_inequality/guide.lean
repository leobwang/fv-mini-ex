/- Guide for H056 (Paley–Zygmund inequality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's (Markov's inequality, a
discriminant bound, a squared bound).
Assumed: Lean basics (E001–E033). Mathlib's measure theory is explained entry by entry.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H056Guide

/-! # Part R · Reference entries -/

/-! ## Integrability and measurability facts -/

/-! ### R1. `MemLp.integrable` · context gains `Integrable f μ` (from a finite second moment)
`hf.integrable one_le_two` uses `1 ≤ 2`: an L² function on a finite measure is L¹. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (G : Prop) (h : Integrable f μ → G) : G := by
  have hi : Integrable f μ := hf.integrable one_le_two
  exact h hi

/-! ### R2. `measurableSet_lt` · context gains `MeasurableSet {ω | g ω < f ω}`
Both sides must be `Measurable`; a constant is `measurable_const`. -/
example {Ω : Type} [MeasurableSpace Ω] (f : Ω → ℝ) (hf : Measurable f) (c : ℝ) (G : Prop)
    (h : MeasurableSet {ω | c < f ω} → G) : G := by
  have hA : MeasurableSet {ω | c < f ω} := measurableSet_lt measurable_const hf
  exact h hA

/-! ### R3. `Integrable.mul_bdd` · goal `Integrable (fun ω => f ω * g ω) μ` → two goals
`f` integrable and `g` bounded by `c` almost everywhere: measurability of `g`, then the bound. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hb : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1) :
    Integrable (fun ω => f ω * g ω) μ := by
  refine hf.mul_bdd (c := 1) ?_ ?_
  exact hg
  exact hb

/-! ### R4. `Measurable.aestronglyMeasurable` · goal `AEStronglyMeasurable g μ` → `Measurable g` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ) (h : Measurable g) :
    AEStronglyMeasurable g μ := by
  apply Measurable.aestronglyMeasurable
  exact h

/-! ### R5. `Measurable.indicator` · goal `Measurable (A.indicator f)` → `Measurable f`, `MeasurableSet A`
The constant function `1 : Ω → ℝ` is `measurable_const`. -/
example {Ω : Type} [MeasurableSpace Ω] (A : Set Ω) (hA : MeasurableSet A) :
    Measurable (A.indicator (1 : Ω → ℝ)) := by
  apply Measurable.indicator
  exact measurable_const
  exact hA

/-! ### R6. `ae_of_all` · goal `∀ᵐ ω ∂μ, p ω` (almost everywhere) → `∀ ω, p ω` (everywhere) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop) (h : ∀ ω, p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  apply ae_of_all
  exact h

/-! ## Indicators, case splits, integrating inequalities -/

/-! ### R7. `by_cases h : Q` · goal list: one goal → two, with `h : Q` and `h : ¬Q` -/
example (Q G : Prop) (h1 : Q → G) (h2 : ¬Q → G) : G := by
  by_cases h : Q
  exact h1 h
  exact h2 h

/-! ### R8. `simp [Set.indicator, h]` · goal: evaluate `{ω | Q ω}.indicator f ω` once `h` decides `Q ω`
`Set.indicator` unfolds to `if ω ∈ A then f ω else 0`; `h` picks the branch. -/
example {Ω : Type} (Q : Ω → Prop) (f : Ω → ℝ) (ω : Ω) (P : ℝ → Prop) (hP : P (f ω)) (h : Q ω) :
    P ({x | Q x}.indicator f ω) := by
  simp [Set.indicator, h]
  exact hP

example {Ω : Type} (Q : Ω → Prop) (f : Ω → ℝ) (ω : Ω) (P : ℝ → Prop) (hP : P 0) (h : ¬Q ω) :
    P ({x | Q x}.indicator f ω) := by
  simp [Set.indicator, h]
  exact hP

/-! ### R9. `calc` · goal `a ≤ c` → one goal per step (`a ≤ b`, then `b = c`) -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b = c) : a ≤ c := by
  calc a ≤ b := ?_
    _ = c := ?_
  exact h1
  exact h2

/-! ### R10. `integral_mono` · goal `∫ f ≤ ∫ g` → the pointwise goal `f ω ≤ g ω`
Needs both integrable. Its last argument has type `f ≤ g`, which for functions means `∀ ω, f ω ≤ g ω`,
so `fun ω => ?_` leaves one goal for a fixed `ω`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (h : ∀ ω, f ω ≤ g ω) : ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ := by
  refine integral_mono hf hg fun ω => ?_
  exact h ω

/-! ### R11. `integrable_const`, `Integrable.add` · context gains `Integrable (fun ω => c + f ω) μ`
`integrable_const c` needs a finite measure (a probability measure is one). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (c : ℝ) (G : Prop) (h : Integrable (fun ω => c + f ω) μ → G) : G := by
  have hs : Integrable (fun ω => c + f ω) μ := (integrable_const c).add hf
  exact h hs

/-! ### R12. `mul_nonneg` · goal `0 ≤ a * b` → `0 ≤ a`, `0 ≤ b` -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  apply mul_nonneg
  exact ha
  exact hb

/-! ### R13. `integral_nonneg` · goal `0 ≤ ∫ f` → `0 ≤ f` (pointwise: `∀ ω, 0 ≤ f ω`)
A hypothesis `hnn : ∀ ω, 0 ≤ f ω` is accepted as `0 ≤ f`: `integral_nonneg hnn`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hnn : ∀ ω, 0 ≤ f ω) :
    0 ≤ ∫ ω, f ω ∂μ := by
  apply integral_nonneg
  exact hnn

/-! ### R14. `linarith` · closes a linear (in)equality from the hypotheses; reads `¬ a < b` as `b ≤ a` -/
example (x c : ℝ) (h : ¬c < x) : x ≤ c + 0 := by
  linarith

/-! ## Computing integrals -/

/-! ### R15. `integral_add` · `∫ (f + g) = ∫ f + ∫ g`, given `Integrable f μ` and `Integrable g μ`
`rw` finds `∫ ω, f ω + g ω ∂μ` only when `hf hg` are stated about `fun ω => …` with the same body. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ ω, f ω ∂μ + ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω + g ω ∂μ) := by
  rw [integral_add hf hg]
  exact h

/-! ### R16. `integral_const`, then `simp` · goal: `∫ ω, c ∂μ` → `c` for a probability measure -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ)
    (P : ℝ → Prop) (h : P c) : P (∫ _ω, c ∂μ) := by
  rw [integral_const]
  simp
  exact h

/-! ### R17. `MemLp.integrable_sq` · context gains `Integrable (fun ω => f ω ^ 2) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (G : Prop)
    (h : Integrable (fun ω => f ω ^ 2) μ → G) : G := by
  have h2 := hf.integrable_sq
  exact h h2

/-! ### R18. `Integrable.indicator` · context gains `Integrable (A.indicator 1) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω)
    (hA : MeasurableSet A) (G : Prop) (h : Integrable (A.indicator (1 : Ω → ℝ)) μ → G) : G := by
  have hi : Integrable (A.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hA
  exact h hi

/-! ### R19. `linear_combination e * h` · closes `a = b` when `a - b = e * (lhs h - rhs h)` by `ring` -/
example (x y t : ℝ) (h : x ^ 2 = x) : y + t * t * x ^ 2 = y + t * t * x := by
  linear_combination (t * t) * h

/-! ### R20. `sq_nonneg` · context gains `0 ≤ a ^ 2` (a square is nonnegative) -/
example (a : ℝ) (G : Prop) (h : 0 ≤ a ^ 2 → G) : G := by
  have hs := sq_nonneg a
  exact h hs

/-! ### R21. `Integrable.const_mul` · context gains `Integrable (fun ω => c * f ω) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)
    (G : Prop) (h : Integrable (fun ω => c * f ω) μ → G) : G := by
  have hc := hf.const_mul c
  exact h hc

/-! ### R22. `integral_const_mul` · goal: `∫ ω, c * f ω ∂μ` → `c * ∫ ω, f ω ∂μ` (no side goal) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) (P : ℝ → Prop)
    (h : P (c * ∫ ω, f ω ∂μ)) : P (∫ ω, c * f ω ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! ### R23. `integral_indicator_one` · goal: `∫ ω, A.indicator 1 ω ∂μ` → `μ.real A` (needs `MeasurableSet A`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (P : ℝ → Prop) (h : P (μ.real A)) : P (∫ ω, A.indicator 1 ω ∂μ) := by
  rw [integral_indicator_one hA]
  exact h

/-! ### R24. `rw [e] at h` · context: rewrites the hypothesis `h` instead of the goal -/
example (a b : ℝ) (e : a = b) (P : ℝ → Prop) (h : P a) : P b := by
  rw [e] at h
  exact h

/-! ## The discriminant (Cauchy–Schwarz) and the last step -/

/-! ### R25. `discrim_le_zero` · context gains `discrim a b c ≤ 0` from `∀ x, 0 ≤ a * (x * x) + b * x + c` -/
example (a b c : ℝ) (hq : ∀ x : ℝ, 0 ≤ a * (x * x) + b * x + c) (G : Prop)
    (h : discrim a b c ≤ 0 → G) : G := by
  have hd := discrim_le_zero hq
  exact h hd

/-! ### R26. `rw [discrim] at h` · context: `discrim a b c` → `b ^ 2 - 4 * a * c` -/
example (a b c : ℝ) (hd : discrim a b c ≤ 0) : b ^ 2 ≤ 4 * a * c := by
  rw [discrim] at hd
  linarith

/-! ### R27. `nlinarith` · closes a goal that needs products of hypotheses (`linarith` does not multiply) -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  nlinarith

/-! ### R28. `pow_le_pow_left₀` · goal `a ^ n ≤ b ^ n` → `0 ≤ a`, `a ≤ b` -/
example (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ n ≤ b ^ n := by
  apply pow_le_pow_left₀
  exact ha
  exact hab

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Markov's inequality `c · P(f > c) ≤ E f`: R2, R18, R23, R22, R21, R10, R7, R8, R14 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfi : Integrable f μ) (hpos : ∀ ω, 0 ≤ f ω) (c : ℝ) :
    c * μ.real {ω | c < f ω} ≤ ∫ ω, f ω ∂μ := by
  have hA : MeasurableSet {ω | c < f ω} := measurableSet_lt measurable_const hf
  have hi : Integrable ({ω | c < f ω}.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hA
  rw [← integral_indicator_one hA, ← integral_const_mul]
  refine integral_mono (hi.const_mul c) hfi fun ω => ?_
  by_cases h : c < f ω
  · simp [Set.indicator, h]
    linarith
  · simp [Set.indicator, h]
    exact hpos ω

/-! ### W2. A quadratic that is never negative has a nonpositive discriminant: R25, R26, R14 -/
example (b c : ℝ) (hq : ∀ t : ℝ, 0 ≤ 1 * (t * t) + b * t + c) : b ^ 2 ≤ 4 * c := by
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  linarith

/-! ### W3. Squaring a bound inside `calc`: `ring`, R28, R14 -/
example (a b : ℝ) (ha : 0 ≤ a) (hab : 2 * a ≤ b) : 4 * a ^ 2 ≤ b ^ 2 := by
  calc 4 * a ^ 2 = (2 * a) ^ 2 := by ring
    _ ≤ b ^ 2 := pow_le_pow_left₀ (by linarith) hab 2

end H056Guide

/- Guide for H058 (Empirical frequencies converge).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal and `k : … → G` only consumes a new hypothesis.
Part W: worked combinations on objects that are NOT the exercise's (`x ^ 2` near `1`, generic sequences).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H058Guide

open MeasureTheory ProbabilityTheory Filter Topology

/-! # Part R · Reference entries -/

/-! ## Part 1 · One event: the strong law for an indicator (milestone `frequency_tendsto`) -/

/-! ### R1. `set x := e with hx` · context gains `x : α := e` and `hx : x = e`; goal: `e` → `x` -/
example {α : Type} (e : α) (P : α → Prop) (h : ∀ y, P y) : P e := by
  set x := e with hx
  exact h x

/-! ### R2. `Measurable.indicator` (with `measurable_const`) · goal list: `Measurable (A.indicator g)`
→ `Measurable g` and `MeasurableSet A`. Term form: `measurable_const.indicator hA`. -/
example {α : Type} [MeasurableSpace α] (A : Set α) (hA : MeasurableSet A) :
    Measurable (A.indicator fun _ => (1 : ℝ)) := by
  apply Measurable.indicator
  · exact measurable_const
  · exact hA

/-! ### R3. `Measurable.comp` · `hf.comp hg : Measurable (f ∘ g)` · context gains it -/
example {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α] (f : α → ℝ) (g : Ω → α)
    (hf : Measurable f) (hg : Measurable g) (G : Prop) (k : Measurable (f ∘ g) → G) : G := by
  have h := hf.comp hg
  exact k h

/-! ### R4. `Measurable.aestronglyMeasurable` · `Measurable f → AEStronglyMeasurable f μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (G : Prop)
    (k : AEStronglyMeasurable f μ → G) : G := by
  have h := hf.aestronglyMeasurable (μ := μ)
  exact k h

/-! ### R5. `Integrable.of_bound` · goal: `Integrable f μ` → `∀ᵐ x ∂μ, ‖f x‖ ≤ C`
Needs a finite measure; `IsProbabilityMeasure μ` gives `IsFiniteMeasure μ` automatically. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (C : ℝ) (h : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) : Integrable f μ := by
  refine Integrable.of_bound hf C ?_
  exact h

/-! ### R6. `Eventually.of_forall` · goal: `∀ᵐ ω ∂μ, p ω` → context gains `ω`, goal `p ω` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop) (h : ∀ ω, p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  refine Eventually.of_forall fun ω => ?_
  exact h ω

/-! ### R7. `simp only [Set.indicator, Function.comp]` · goal: `(A.indicator g ∘ Z) ω` →
`if Z ω ∈ A then g (Z ω) else 0` -/
example {Ω α : Type} (A : Set α) (Z : Ω → α) (ω : Ω) (P : ℝ → Prop)
    (h : ∀ c : ℝ, P c) : P (((A.indicator fun _ => (1 : ℝ)) ∘ Z) ω) := by
  simp only [Set.indicator, Function.comp]
  exact h _

/-! ### R8. `split_ifs` · goal list: `P (if c then x else y)` → `P x` (with `c`), `P y` (with `¬c`) -/
example (c : Prop) [Decidable c] (P : ℝ → Prop) (h1 : P 1) (h0 : P 0) :
    P (if c then 1 else 0) := by
  split_ifs
  exacts [h1, h0]

/-! ### R9. `simp` (`norm_one`, `norm_zero`) · closes `‖1‖ ≤ 1` and `‖0‖ ≤ 1` -/
example : ‖(1 : ℝ)‖ ≤ 1 ∧ ‖(0 : ℝ)‖ ≤ 1 := by
  simp

/-! ### R10. `Pairwise r` is `∀ ⦃i j⦄, i ≠ j → r i j` · `intro i j hij` (or `fun i j hij => …`) -/
example (r : ℕ → ℕ → Prop) (h : ∀ i j, i ≠ j → r i j) : Pairwise r := by
  intro i j hij
  exact h i j hij

/-! ### R11. `IndepFun.comp` · `Y ⟂ᵢ[μ] Z → Measurable φ → Measurable ψ → (φ ∘ Y) ⟂ᵢ[μ] (ψ ∘ Z)` -/
example {Ω β γ : Type} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure Ω)
    (Y Z : Ω → β) (φ ψ : β → γ) (hYZ : Y ⟂ᵢ[μ] Z) (hφ : Measurable φ) (hψ : Measurable ψ)
    (G : Prop) (k : (φ ∘ Y) ⟂ᵢ[μ] (ψ ∘ Z) → G) : G := by
  have h := hYZ.comp hφ hψ
  exact k h

/-! ### R12. `IdentDistrib.comp` · `IdentDistrib Y Z μ μ → Measurable φ → IdentDistrib (φ ∘ Y) (φ ∘ Z) μ μ` -/
example {Ω β γ : Type} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure Ω)
    (Y Z : Ω → β) (φ : β → γ) (hYZ : IdentDistrib Y Z μ μ) (hφ : Measurable φ)
    (G : Prop) (k : IdentDistrib (φ ∘ Y) (φ ∘ Z) μ μ → G) : G := by
  have h := hYZ.comp hφ
  exact k h

/-! ### R13. `rfl` · an indicator composed with `Z` is the indicator of the preimage `Z ⁻¹' A`
Both sides unfold to `fun ω => if Z ω ∈ A then c else 0`. -/
example {Ω α : Type} (A : Set α) (Z : Ω → α) (c : ℝ) :
    (A.indicator fun _ => c) ∘ Z = (Z ⁻¹' A).indicator fun _ => c := by
  rfl

/-! ### R14. `integral_indicator_const` · `MeasurableSet S → ∫ ω, S.indicator (fun _ => e) ω ∂μ = μ.real S • e` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (hS : MeasurableSet S) (e : ℝ)
    (P : ℝ → Prop) (h : P (μ.real S • e)) : P (∫ ω, S.indicator (fun _ => e) ω ∂μ) := by
  rw [integral_indicator_const e hS]
  exact h

/-! ### R15. `smul_eq_mul`, then `mul_one` · goal: `a • b` → `a * b`; `a * 1` → `a` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R16. `strong_law_ae` · context gains the strong law of large numbers for `Y` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hint : Integrable (Y 0) μ) (hind : Pairwise fun i j => Y i ⟂ᵢ[μ] Y j)
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (G : Prop)
    (k : (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y i ω) atTop
      (𝓝 (∫ ω, Y 0 ω ∂μ))) → G) : G := by
  have hslln := strong_law_ae Y hint hind hid
  exact k hslln

/-! ### R17. `filter_upwards [h] with ω hω` · goal `∀ᵐ ω ∂μ, q ω` → context gains `ω`, `hω : p ω`;
goal `q ω`. Works for every filter (`∀ᶠ n in atTop` too), and `with` may name further `∀`/`→` binders. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → Prop) (h : ∀ᵐ ω ∂μ, p ω)
    (hpq : ∀ ω, p ω → q ω) : ∀ᵐ ω ∂μ, q ω := by
  filter_upwards [h] with ω hω
  exact hpq ω hω

example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop) (R Q : Ω → ℝ → Prop)
    (h : ∀ᵐ ω ∂μ, p ω) (hpq : ∀ ω, p ω → ∀ t, R ω t → Q ω t) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, R ω t → Q ω t := by
  filter_upwards [h] with ω hω t ht
  exact hpq ω hω t ht

/-! ### R18. `rw [e] at h` · context: `h : P a` → `h : P b` (for `e : a = b`) -/
example (a b : ℝ) (e : a = b) (P : ℝ → Prop) (h : P a) : P b := by
  rw [e] at h
  exact h

/-! ### R19. `convert h using 2 with n` · goal `Tendsto f l L` with `h : Tendsto g l L` →
the pointwise difference `f n = g n` -/
example (a b : ℕ → ℝ) (L : ℝ) (h : Tendsto (fun n => (b n)⁻¹ • a n) atTop (𝓝 L))
    (hab : ∀ n, a n / b n = (b n)⁻¹ • a n) : Tendsto (fun n => a n / b n) atTop (𝓝 L) := by
  convert h using 2 with n
  exact hab n

/-! ### R20. `Finset.sum_boole` · `(∑ i ∈ s, if p i then 1 else 0) = ↑#{i ∈ s | p i}` -/
example {ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (P : ℝ → Prop)
    (h : P ((s.filter p).card : ℝ)) : P (∑ i ∈ s, if p i then 1 else 0) := by
  rw [Finset.sum_boole]
  exact h

/-! ### R21. `div_eq_inv_mul` · `a / b = b⁻¹ * a` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (b⁻¹ * a)) : P (a / b) := by
  rw [div_eq_inv_mul]
  exact h

/-! ## Part 2 · All rationals at once (milestone `frequency_tendsto_rat`) -/

/-! ### R22. `ae_all_iff` · goal: `∀ᵐ ω, ∀ q, p ω q` → `∀ q, ∀ᵐ ω, p ω q` (index type countable: `ℚ`, `ℕ`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → ℚ → Prop)
    (h : ∀ q, ∀ᵐ ω ∂μ, p ω q) : ∀ᵐ ω ∂μ, ∀ q : ℚ, p ω q := by
  rw [ae_all_iff]
  exact h

/-! ### R23. `change` · goal: `{ω | Z ω ≤ c}` → `Z ⁻¹' Set.Iic c` (the same set by definition) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) (c : ℝ) (P : ℝ → Prop)
    (h : P (μ.real (Z ⁻¹' Set.Iic c))) : P (μ.real {ω | Z ω ≤ c}) := by
  change P (μ.real (Z ⁻¹' Set.Iic c))
  exact h

/-! ### R24. `measurableSet_Iic` · closes `MeasurableSet (Set.Iic c)` -/
example (c : ℝ) : MeasurableSet (Set.Iic c) := by
  exact measurableSet_Iic

/-! ## Part 3 · Monotone in the threshold (milestone `frequency_mono`) -/

/-! ### R25. `gcongr` · goal: `a / c ≤ b / c` → `a ≤ b` (side goal `0 ≤ c` closed by itself) -/
example (a b c : ℝ) (hc : 0 ≤ c) (h : 0 ≤ b - a) : a / c ≤ b / c := by
  gcongr
  linarith

/-! ### R26. `gcongr with i hi` · goal: `↑#{i ∈ s | p i} ≤ ↑#{i ∈ s | q i}` → `p i → q i`
`gcongr` goes through the cast, `Finset.card` and `Finset.filter` in one call. -/
example (n : ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ i, p i → q i) :
    (((Finset.range n).filter p).card : ℝ) ≤ ((Finset.range n).filter q).card := by
  gcongr with i hi
  exact h i

/-! ## Part 4 · The squeeze at a continuity point (`empirical_cdf`) -/

/-! ### R27. `rw [tendsto_order]` · goal: `Tendsto u atTop (𝓝 L)` → lower and upper eventual bounds -/
example (u : ℕ → ℝ) (L : ℝ)
    (h : (∀ a < L, ∀ᶠ n in atTop, a < u n) ∧ ∀ a > L, ∀ᶠ n in atTop, u n < a) :
    Tendsto u atTop (𝓝 L) := by
  rw [tendsto_order]
  exact h

/-! ### R28. `(tendsto_order.1 hu).1 a ha` · context gains `∀ᶠ n in atTop, a < u n` (`.2` for `u n < a`) -/
example (u : ℕ → ℝ) (L a : ℝ) (hu : Tendsto u atTop (𝓝 L)) (ha : a < L) (G : Prop)
    (k : (∀ᶠ n in atTop, a < u n) → G) : G := by
  have h := (tendsto_order.1 hu).1 a ha
  exact k h

/-! ### R29. `lt_mem_nhds`, `gt_mem_nhds` · `a < b → ∀ᶠ x in 𝓝 b, a < x`; `b < a → ∀ᶠ x in 𝓝 b, x < a` -/
example (a b : ℝ) (ha : a < b) (G : Prop) (k : (∀ᶠ x in 𝓝 b, a < x) → G) : G := by
  have h := lt_mem_nhds ha
  exact k h

/-! ### R30. `ContinuousAt.eventually` (`Tendsto.eventually`) · from `ht : ContinuousAt F t` and
`∀ᶠ y in 𝓝 (F t), p y`, context gains `∀ᶠ s in 𝓝 t, p (F s)` -/
example (F : ℝ → ℝ) (t a : ℝ) (ht : ContinuousAt F t) (hev : ∀ᶠ y in 𝓝 (F t), a < y) (G : Prop)
    (k : (∀ᶠ s in 𝓝 t, a < F s) → G) : G := by
  have h := ht.eventually hev
  exact k h

/-! ### R31. `Metric.eventually_nhds_iff` · context: `∀ᶠ y in 𝓝 x, p y` → `δ > 0` and a `δ`-ball -/
example (x : ℝ) (p : ℝ → Prop) (hev : ∀ᶠ y in 𝓝 x, p y) (G : Prop)
    (k : ∀ δ > 0, (∀ ⦃y : ℝ⦄, dist y x < δ → p y) → G) : G := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hev
  exact k δ hδ h

/-! ### R32. `exists_rat_btwn` · context: from `x < y`, a rational `q` with `x < ↑q < y` -/
example (x y : ℝ) (hxy : x < y) (G : Prop) (k : ∀ q : ℚ, x < q → (q : ℝ) < y → G) : G := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy
  exact k q hq1 hq2

/-! ### R33. `linarith` · closes a linear (in)equality that follows from hypotheses by adding them -/
example (t δ : ℝ) (hδ : δ > 0) : t - δ < t := by
  linarith

/-! ### R34. `Real.dist_eq` · `dist x y = |x - y|` -/
example (x y : ℝ) (P : ℝ → Prop) (h : P |x - y|) : P (dist x y) := by
  rw [Real.dist_eq]
  exact h

/-! ### R35. `abs_sub_lt_iff` · goal: `|a - b| < c` → `a - b < c ∧ b - a < c` -/
example (a b c : ℝ) (h : a - b < c ∧ b - a < c) : |a - b| < c := by
  rw [abs_sub_lt_iff]
  exact h

/-! ### R36. `h₁.trans_le h₂`, `h₂.trans_lt h₁`, `h.le` · chain `<` with `≤`; weaken `<` to `≤`
`a < b → b ≤ c → a < c` (`lt_of_lt_of_le`), `a ≤ b → b < c → a < c` (`lt_of_le_of_lt`). -/
example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  exact h₁.trans_le h₂

example (a b c : ℝ) (h₂ : a ≤ b) (h₁ : b < c) : a < c := by
  exact h₂.trans_lt h₁

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A point in `(t - δ, t)` is within `δ` of `t`: R34, R35, then R33 on both halves -/
example (t δ y : ℝ) (h1 : t - δ < y) (h2 : y < t) : dist y t < δ := by
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · linarith
  · linarith

/-! ### W2. Continuity + a strict bound + density of `ℚ`: R29, R30, R31, R32, W1
`x ↦ x ^ 2` is continuous at `1` and `1 ^ 2 < 2`, so some rational `q > 1` still has `q ^ 2 < 2`. -/
example : ∃ q : ℚ, 1 < (q : ℝ) ∧ (q : ℝ) ^ 2 < 2 := by
  have hc : ContinuousAt (fun x : ℝ => x ^ 2) 1 := (continuous_pow 2).continuousAt
  have hlt : (fun x : ℝ => x ^ 2) 1 < 2 := by norm_num
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hlt))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (1 : ℝ) < 1 + δ by linarith)
  refine ⟨q, hq1, h ?_⟩
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-! ### W3. Lifting an eventual bound along `u ≤ v`: R17 on `atTop`, then R36 -/
example (u v : ℕ → ℝ) (a : ℝ) (huv : ∀ n, u n ≤ v n) (hu : ∀ᶠ n in atTop, a < u n) :
    ∀ᶠ n in atTop, a < v n := by
  filter_upwards [hu] with n hn
  exact hn.trans_le (huv n)

end H058Guide

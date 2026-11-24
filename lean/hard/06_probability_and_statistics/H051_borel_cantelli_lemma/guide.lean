/- Guide for H051 (Borel–Cantelli lemma).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal and `k : … → G` only consumes a new hypothesis.
Part W: worked combinations on objects that are NOT the exercise's (null unions, `f = 0` a.e.,
a squeeze in `ℝ≥0∞`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H051Guide

open MeasureTheory Filter Topology
open scoped ENNReal

/-! # Part R · Reference entries -/

/-! ## Part 1 · `limsup` of sets as `⋂ ⋃` (milestone `limsup_subset`) -/

/-! ### R1. `limsup_eq_iInf_iSup_of_nat'` · `limsup u atTop = ⨅ n, ⨆ i, u (i + n)` · goal
On sets, `⨅` is the intersection `⋂` and `⨆` is the union `⋃` (the same constants). -/
example {Ω : Type} (A : ℕ → Set Ω) (P : Set Ω → Prop) (h : P (⨅ n, ⨆ i, A (i + n))) :
    P (limsup A atTop) := by
  rw [limsup_eq_iInf_iSup_of_nat']
  exact h

/-! ### R2. `iInf_le` · `iInf_le f i : ⨅ j, f j ≤ f i` · closes the goal
On sets `≤` is `⊆` by definition, so `exact iInf_le _ i` closes a `⊆` goal too. -/
example {Ω : Type} (B : ℕ → Set Ω) (i : ℕ) : ⨅ j, B j ⊆ B i := by
  exact iInf_le _ i

/-! ## Part 2 · Measure of the limsup (milestone `measure_limsup_le`) -/

/-! ### R3. `calc` · goal `a ≤ c` → one goal per step `a ≤ b`, `b ≤ c` (`_` is the previous right side) -/
example {α : Type} [Preorder α] (a b c : α) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  calc a ≤ b := h₁
    _ ≤ c := h₂

/-! ### R4. `measure_mono` · `S ⊆ T → μ S ≤ μ T` (monotonicity of a measure) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S T : Set Ω) (hST : S ⊆ T) :
    μ S ≤ μ T := by
  exact measure_mono hST

/-! ### R5. `measure_iUnion_le` · `μ (⋃ i, B i) ≤ ∑' i, μ (B i)` (countable subadditivity)
The index type needs `[Countable ι]`; `ℕ` and any subtype of a countable type qualify. No
measurability is needed. -/
example {Ω ι : Type} [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω) (B : ι → Set Ω) :
    μ (⋃ i, B i) ≤ ∑' i, μ (B i) := by
  exact measure_iUnion_le B

/-! ## Part 3 · "not eventually" is the limsup (milestone `setOf_not_eventually`) -/

/-! ### R6. `ext ω` (lemma `Set.ext`) · goal `S = T` of sets → context gains `ω`, goal `ω ∈ S ↔ ω ∈ T` -/
example {Ω : Type} (S T : Set Ω) (h : ∀ ω, ω ∈ S ↔ ω ∈ T) : S = T := by
  ext ω
  exact h ω

/-! ### R7. `limsup_eq_iInf_iSup_of_nat` · `limsup u atTop = ⨅ n, ⨆ i ≥ n, u i` · goal
The unshifted form: `⨆ i ≥ n, u i` is `⨆ i, ⨆ (_ : i ≥ n), u i`. -/
example {Ω : Type} (A : ℕ → Set Ω) (P : Set Ω → Prop) (h : P (⨅ n, ⨆ i ≥ n, A i)) :
    P (limsup A atTop) := by
  rw [limsup_eq_iInf_iSup_of_nat]
  exact h

/-! ### R8. `simp` on membership (`Set.mem_iInter`, `Set.mem_iUnion`, `exists_prop`) · goal
`ω ∈ ⨅ n, ⨆ i ≥ n, A i` → `∀ n, ∃ i, n ≤ i ∧ ω ∈ A i` ("ω is in infinitely many `A i`"). -/
example {Ω : Type} (A : ℕ → Set Ω) (ω : Ω) (h : ∀ n, ∃ i, n ≤ i ∧ ω ∈ A i) :
    ω ∈ ⨅ n, ⨆ i ≥ n, A i := by
  simp
  exact h

/-! ### R9. `Filter.not_eventually`, `Filter.frequently_atTop` (both `simp` lemmas) · goal
`¬∀ᶠ n in atTop, ¬p n` → `∃ᶠ n in atTop, p n` → `∀ a, ∃ b ≥ a, p b`. -/
example (p : ℕ → Prop) (P : Prop → Prop) (h : P (∀ a, ∃ b ≥ a, p b)) :
    P (¬∀ᶠ n in atTop, ¬p n) := by
  rw [Filter.not_eventually]
  simp only [not_not]
  rw [Filter.frequently_atTop]
  exact h

/-! ## Part 4 · Infinitely many indices give one outside `F` (milestone `setOf_infinite_subset`) -/

/-! ### R10. `intro ω hω` on `S ⊆ T` · `S ⊆ T` means `∀ ω, ω ∈ S → ω ∈ T`, so `intro` opens it -/
example {Ω : Type} (S T : Set Ω) (h : ∀ ω, ω ∈ S → ω ∈ T) : S ⊆ T := by
  intro ω hω
  exact h ω hω

/-! ### R11. `Finset.finite_toSet` · `F.finite_toSet : (↑F : Set ι).Finite` · context
`↑F` is the finset `F` seen as a set; `x ∈ ↑F ↔ x ∈ F` holds by definition. -/
example {ι : Type} (F : Finset ι) (G : Prop) (k : (↑F : Set ι).Finite → G) : G := by
  have h := F.finite_toSet
  exact k h

/-! ### R12. `Set.Infinite.sdiff` · `S.Infinite → T.Finite → (S \ T).Infinite` · context -/
example {ι : Type} (S T : Set ι) (hS : S.Infinite) (hT : T.Finite) (G : Prop)
    (k : (S \ T).Infinite → G) : G := by
  have h := hS.sdiff hT
  exact k h

/-! ### R13. `Set.Infinite.nonempty` · `S.Infinite → S.Nonempty` · context -/
example {ι : Type} (S : Set ι) (hS : S.Infinite) (G : Prop) (k : S.Nonempty → G) : G := by
  have h := hS.nonempty
  exact k h

/-! ### R14. `obtain ⟨i, hi, hiT⟩` on `(S \ T).Nonempty` · context: one element and its two facts
`(S \ T).Nonempty` is `∃ i, i ∈ S \ T`, and `i ∈ S \ T` is `i ∈ S ∧ i ∉ T` by definition.
A hypothesis `hS : S.Infinite` with `S = {i | …}` is also `¬ S.Finite` by definition. -/
example {ι : Type} (S T : Set ι) (hne : (S \ T).Nonempty) (G : Prop)
    (k : ∀ i, i ∈ S → i ∉ T → G) : G := by
  obtain ⟨i, hi, hiT⟩ := hne
  exact k i hi hiT

/-! ### R15. Subtype `{x // x ∉ F}` · an element is `⟨x, hx⟩` with `hx : x ∉ F`; `↑y` (or `y.1`) is `x` -/
example {ι : Type} (F : Finset ι) (x : ι) (hx : x ∉ F) (P : ι → Prop) (h : P x) :
    P (↑(⟨x, hx⟩ : {y // y ∉ F})) := by
  exact h

/-! ### R16. `Set.mem_iUnion` · `ω ∈ ⋃ i, B i ↔ ∃ i, ω ∈ B i`; `.mpr ⟨i, h⟩` proves membership -/
example {Ω ι : Type} (B : ι → Set Ω) (ω : Ω) (i : ι) (h : ω ∈ B i) : ω ∈ ⋃ j, B j := by
  rw [Set.mem_iUnion]
  exact ⟨i, h⟩

/-! ## Part 5 · Squeezing a measure to `0` (`borel_cantelli`) -/

/-! ### R17. `le_antisymm` · `a ≤ b → b ≤ a → a = b` · goal `a = b` → goals `a ≤ b`, `b ≤ a` -/
example {α : Type} [PartialOrder α] (a b : α) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  apply le_antisymm
  exact h₁
  exact h₂

/-! ### R18. `bot_le` · `⊥ ≤ a`; in `ℝ≥0∞` the bottom `⊥` is `0`, so it closes `0 ≤ a` -/
example (a : ℝ≥0∞) : 0 ≤ a := by
  exact bot_le

/-! ### R19. `ge_of_tendsto'` · `Tendsto f l (𝓝 a) → (∀ c, b ≤ f c) → b ≤ a` · goal
A constant below every term of a convergent sequence is below the limit. `l` must be a proper
filter (`atTop` on `ℕ` or on `Finset ι` is). After `apply ge_of_tendsto' hf` the goal is the bound. -/
example (f : ℕ → ℝ≥0∞) (a b : ℝ≥0∞) (hf : Tendsto f atTop (𝓝 a)) (hb : ∀ c, b ≤ f c) :
    b ≤ a := by
  apply ge_of_tendsto' hf
  exact hb

/-! ### R20. `ENNReal.tendsto_sum_nat_add` · `∑' i, f i ≠ ∞ → Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)`
The tails of a finite `ℝ≥0∞`-series tend to `0`. -/
example (f : ℕ → ℝ≥0∞) (hf : ∑' i, f i ≠ ∞) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  exact ENNReal.tendsto_sum_nat_add f hf

/-! ## Part 6 · Almost everywhere = complement is null (`ae_finitely_many`) -/

/-! ### R21. `ae_iff` · `(∀ᵐ ω ∂μ, p ω) ↔ μ {ω | ¬p ω} = 0` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop)
    (h : μ {ω | ¬p ω} = 0) : ∀ᵐ ω ∂μ, p ω := by
  rw [ae_iff]
  exact h

/-! ## Part 7 · Tails over finsets (`ae_finite`) -/

/-! ### R22. `ENNReal.tendsto_tsum_compl_atTop_zero` · tails indexed by finsets tend to `0`
`∑' x, f x ≠ ∞ → Tendsto (fun F : Finset ι => ∑' b : {x // x ∉ F}, f ↑b) atTop (𝓝 0)`. On `Finset ι`,
`atTop` means "`F` grows to contain any given finite set". -/
example {ι : Type} (f : ι → ℝ≥0∞) (hf : ∑' i, f i ≠ ∞) :
    Tendsto (fun F : Finset ι => ∑' b : {x // x ∉ F}, f ↑b) atTop (𝓝 0) := by
  exact ENNReal.tendsto_tsum_compl_atTop_zero hf

/-! ### R23. `h₁.trans h₂` (`LE.le.trans`) · `a ≤ b → b ≤ c → a ≤ c` in one term (the one-line `calc`) -/
example {α : Type} [Preorder α] (a b c : α) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  exact h₁.trans h₂

/-! ### R24. `refine … fun F => ?_` · goal list: the hole under `fun F =>` becomes a goal with `F` in context -/
example {ι : Type} (Q : Finset ι → Prop) (G : Prop) (k : (∀ F, Q F) → G) (h : ∀ F, Q F) : G := by
  refine k fun F => ?_
  exact h F

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A countable union of null sets is null: R17, R23, R5, then `simp [h]`, R18 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (B : ℕ → Set Ω) (hB : ∀ i, μ (B i) = 0) :
    μ (⋃ i, B i) = 0 := by
  apply le_antisymm
  · exact (measure_iUnion_le B).trans (by simp [hB])
  · exact bot_le

/-! ### W2. A squeeze in `ℝ≥0∞`: a constant below `(↑n)⁻¹` for every `n` is `0` (R17, R19, R18)
`ENNReal.tendsto_inv_nat_nhds_zero : Tendsto (fun n : ℕ => (↑n : ℝ≥0∞)⁻¹) atTop (𝓝 0)`; in `ℝ≥0∞`,
`0⁻¹ = ∞`, so the bound at `n = 0` is free. -/
example (b : ℝ≥0∞) (hb : ∀ n : ℕ, b ≤ (n : ℝ≥0∞)⁻¹) : b = 0 := by
  apply le_antisymm
  · exact ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero hb
  · exact bot_le

/-! ### W3. `∀ᵐ` from a null set: R21, then rewrite the set -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (h : μ {ω | f ω ≠ 0} = 0) : ∀ᵐ ω ∂μ, f ω = 0 := by
  rw [ae_iff]
  exact h

end H051Guide

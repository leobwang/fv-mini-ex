/- Guide for H052 (Inclusion–exclusion for n events).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (one set, sums of indicators).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open MeasureTheory

namespace H052Guide

/-! # Part R · Reference entries -/

/-! ## Pointwise: case splits and indicators -/

/-! ### R1. `by_cases h : Q` · goal list: one goal → two, with `h : Q` and `h : ¬Q` -/
example (Q G : Prop) (yes : Q → G) (no : ¬Q → G) : G := by
  by_cases h : Q
  · exact yes h
  · exact no h

/-! ### R2. `obtain ⟨i, hi, hx⟩ := h` · context: `h : ∃ i ∈ s, Q i` → `i`, `hi : i ∈ s`, `hx : Q i` -/
example {ι : Type} (s : Finset ι) (Q : ι → Prop) (G : Prop) (h : ∃ i ∈ s, Q i)
    (k : ∀ i, i ∈ s → Q i → G) : G := by
  obtain ⟨i, hi, hx⟩ := h
  exact k i hi hx

/-! ### R3. `Set.mem_iUnion₂` · goal: `x ∈ ⋃ i ∈ s, B i` ↔ `∃ i ∈ s, x ∈ B i`
As a term: `Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩ : x ∈ ⋃ i ∈ s, B i`. -/
example {Ω ι : Type} (s : Finset ι) (B : ι → Set Ω) (x : Ω) (i : ι) (hi : i ∈ s) (hx : x ∈ B i) :
    x ∈ ⋃ j ∈ s, B j := by
  rw [Set.mem_iUnion₂]
  exact ⟨i, hi, hx⟩

/-! ### R4. `Set.indicator_of_mem` · `x ∈ S → S.indicator f x = f x` · goal -/
example {Ω M : Type} [Zero M] (S : Set Ω) (f : Ω → M) (x : Ω) (hx : x ∈ S) (P : M → Prop)
    (h : P (f x)) : P (S.indicator f x) := by
  rw [Set.indicator_of_mem hx]
  exact h

/-! ### R5. `Pi.one_apply` · `(1 : Ω → ℝ) x = 1` · goal: the constant function `1` applied → `1` -/
example {Ω : Type} (x : Ω) (P : ℝ → Prop) (h : P 1) : P ((1 : Ω → ℝ) x) := by
  rw [Pi.one_apply]
  exact h

/-! ### R6. `Finset.prod_eq_zero` · `i ∈ s → f i = 0 → ∏ j ∈ s, f j = 0` · goal -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (i : ι) (hi : i ∈ s) (hf : f i = 0)
    (P : ℝ → Prop) (h : P 0) : P (∏ j ∈ s, f j) := by
  rw [Finset.prod_eq_zero hi hf]
  exact h

/-! ### R7. `push Not at h` · context: pushes `¬` inward through `∃`, `∀`, `∈` -/
example {ι : Type} (s : Finset ι) (Q : ι → Prop) (G : Prop) (h : ¬∃ i ∈ s, Q i)
    (k : (∀ i ∈ s, ¬Q i) → G) : G := by
  push Not at h
  exact k h

/-! ### R8. `Set.indicator_of_notMem` · `x ∉ S → S.indicator f x = 0` · goal
Without the argument, `rw [Set.indicator_of_notMem]` leaves the side goal `x ∉ S`. -/
example {Ω M : Type} [Zero M] (S : Set Ω) (f : Ω → M) (x : Ω) (hx : x ∉ S) (P : M → Prop)
    (h : P 0) : P (S.indicator f x) := by
  rw [Set.indicator_of_notMem hx]
  exact h

/-! ### R9. `simpa using h` · closes the goal: simplifies `h` and the goal, then `exact h` -/
example {Ω ι : Type} (s : Finset ι) (B : ι → Set Ω) (x : Ω) (h : ∀ i ∈ s, x ∉ B i) :
    x ∉ ⋃ i ∈ s, B i := by
  simpa using h

/-! ### R10. `Finset.prod_eq_one` · `(∀ i ∈ s, f i = 1) → ∏ i ∈ s, f i = 1` · goal -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, f i = 1) (P : ℝ → Prop)
    (h : P 1) : P (∏ i ∈ s, f i) := by
  rw [Finset.prod_eq_one hf]
  exact h

/-! ## Intersections -/

/-! ### R11. `Set.mem_iInter₂` · goal: `x ∈ ⋂ i ∈ s, B i` ↔ `∀ i ∈ s, x ∈ B i` -/
example {Ω ι : Type} (s : Finset ι) (B : ι → Set Ω) (x : Ω) (hx : ∀ i ∈ s, x ∈ B i) :
    x ∈ ⋂ i ∈ s, B i := by
  rw [Set.mem_iInter₂]
  exact hx

/-! ### R12. `simp only [Set.mem_iInter, not_forall]` · goal: `x ∉ ⋂ i ∈ s, B i` → an `∃` -/
example {Ω ι : Type} (s : Finset ι) (B : ι → Set Ω) (x : Ω) (i : ι) (hi : i ∈ s) (hx : x ∉ B i) :
    x ∉ ⋂ j ∈ s, B j := by
  simp only [Set.mem_iInter, not_forall]
  exact ⟨i, hi, hx⟩

/-! ## Expanding a product over subsets -/

/-! ### R13. `Finset.prod_sub` · `∏ (f i - g i) = ∑ t ∈ s.powerset, ((-1)^|t| * ∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i`
Here `f` is the constant `1`, so `∏ i ∈ s \ t, 1` appears. -/
example {ι : Type} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) (P : ℝ → Prop)
    (h : P (∑ t ∈ s.powerset, ((-1) ^ t.card * ∏ _i ∈ s \ t, 1) * ∏ i ∈ t, g i)) :
    P (∏ i ∈ s, (1 - g i)) := by
  rw [Finset.prod_sub]
  exact h

/-! ### R14. `Finset.prod_const_one`, `mul_one` · goal: `∏ _ ∈ u, 1` → `1`, then `a * 1` → `a` -/
example {ι : Type} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) (P : ℝ → Prop)
    (h : P (∑ t ∈ s.powerset, (-1) ^ t.card * ∏ i ∈ t, g i)) :
    P (∑ t ∈ s.powerset, ((-1) ^ t.card * ∏ _i ∈ s \ t, 1) * ∏ i ∈ t, g i) := by
  simp only [Finset.prod_const_one, mul_one]
  exact h

/-! ### R15. `simp_rw [hfg]` (or `simp only [hfg]`) · goal: rewrite UNDER a binder (`∑ i ∈ s,`, `∫ x,`)
`rw [hfg]` fails here: the `i` in `f i` is bound by the sum, and Lean reports
"Did not find an occurrence of the pattern f ?i". -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (hfg : ∀ i, f i = g i) (P : ℝ → Prop)
    (h : P (∑ i ∈ s, g i)) : P (∑ i ∈ s, f i) := by
  simp_rw [hfg]
  exact h

/-! ### R16. `Finset.sum_filter` · `∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0` · goal -/
example {ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → ℝ) (P : ℝ → Prop)
    (h : P (∑ a ∈ s, if p a then f a else 0)) : P (∑ a ∈ s with p a, f a) := by
  rw [Finset.sum_filter]
  exact h

/-! ### R17. `Finset.sum_erase_add` with `Finset.empty_mem_powerset` · goal: split off the `t = ∅` term
`Finset.sum_erase_add s f : a ∈ s → ∑ x ∈ s.erase a, f x + f a = ∑ x ∈ s, f x`; used right to left. -/
example {ι : Type} [DecidableEq ι] (s : Finset ι) (F : Finset ι → ℝ) (P : ℝ → Prop)
    (h : P (∑ t ∈ s.powerset.erase ∅, F t + F ∅)) : P (∑ t ∈ s.powerset, F t) := by
  rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]
  exact h

/-! ### R18. `Finset.card_empty`, `pow_zero`, `one_mul` · goal: `(-1) ^ (∅).card * a` → `a` -/
example {ι : Type} (a : ℝ) (P : ℝ → Prop) (h : P a) :
    P ((-1) ^ (∅ : Finset ι).card * a) := by
  simp only [Finset.card_empty, pow_zero, one_mul]
  exact h

/-! ### R19. `Finset.not_nonempty_empty`, `if_false` · goal: `if (∅).Nonempty then a else 0` → `0` -/
example {ι : Type} (a : ℝ) (P : ℝ → Prop) (h : P 0) :
    P (if (∅ : Finset ι).Nonempty then a else 0) := by
  simp only [Finset.not_nonempty_empty, if_false]
  exact h

/-! ### R20. `simp` on `⋂ i ∈ ∅` · an intersection over no index is `Set.univ`; its indicator is `f` -/
example {Ω ι : Type} (B : ι → Set Ω) (f : Ω → ℝ) (x : Ω) :
    (⋂ i ∈ (∅ : Finset ι), B i).indicator f x = f x := by
  simp

/-! ### R21. `sub_add_cancel_right` · `a - (b + a) = -b` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (-b)) : P (a - (b + a)) := by
  rw [sub_add_cancel_right]
  exact h

/-! ### R22. `Finset.sum_neg_distrib` · `∑ x ∈ s, -f x = -∑ x ∈ s, f x`; right to left: `-` moves inside -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ s, -f i)) :
    P (-∑ i ∈ s, f i) := by
  rw [← Finset.sum_neg_distrib]
  exact h

/-! ### R23. `refine Finset.sum_congr rfl fun t ht => ?_` · goal: two sums over `s` → one term
Context gains the index `t` and `ht : t ∈ s`. -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (hfg : ∀ i ∈ s, f i = g i) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  refine Finset.sum_congr rfl fun t ht => ?_
  exact hfg t ht

/-! ### R24. `Finset.ne_of_mem_erase` · `t ∈ u.erase a → t ≠ a` · context gains `t ≠ a` -/
example {ι : Type} [DecidableEq ι] (u : Finset (Finset ι)) (t : Finset ι) (ht : t ∈ u.erase ∅)
    (G : Prop) (k : t ≠ ∅ → G) : G := by
  have hne : t ≠ ∅ := Finset.ne_of_mem_erase ht
  exact k hne

/-! ### R25. `Finset.nonempty_iff_ne_empty` · `t.Nonempty ↔ t ≠ ∅` · goal -/
example {ι : Type} (t : Finset ι) (hne : t ≠ ∅) : t.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  exact hne

/-! ### R26. `if_pos` · `c → (if c then a else b) = a` · goal -/
example (c : Prop) [Decidable c] (hc : c) (a b : ℝ) (P : ℝ → Prop) (h : P a) :
    P (if c then a else b) := by
  rw [if_pos hc]
  exact h

/-! ### R27. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a ^ n * a)) : P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ## Measurability, integrability, integrals -/

/-! ### R28. `Finset.measurableSet_biUnion` (and `_biInter`) · goal: a finite union → each piece -/
example {Ω ι : Type} [MeasurableSpace Ω] (s : Finset ι) (B : ι → Set Ω)
    (hB : ∀ i, MeasurableSet (B i)) : MeasurableSet (⋃ i ∈ s, B i) := by
  apply Finset.measurableSet_biUnion
  intro i _
  exact hB i

/-! ### R29. `integrable_const` · a constant is integrable for a finite measure · closes the goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (c : ℝ) :
    Integrable (fun _ => c) μ := by
  exact integrable_const c

/-! ### R30. `Integrable.indicator` · `Integrable f μ → MeasurableSet S → Integrable (S.indicator f) μ`
· goal list: one goal → two -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (f : Ω → ℝ)
    (hf : Integrable f μ) (hS : MeasurableSet S) : Integrable (S.indicator f) μ := by
  apply Integrable.indicator
  · exact hf
  · exact hS

/-! ### R31. `Integrable.const_mul` · `Integrable f μ → Integrable (fun x => c * f x) μ` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : Integrable f μ) : Integrable (fun x => c * f x) μ := by
  apply Integrable.const_mul
  exact hf

/-! ### R32. `integral_indicator_one` · `MeasurableSet S → ∫ x, S.indicator 1 x ∂μ = μ.real S`
Right to left turns a measure into an integral. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (hS : MeasurableSet S)
    (P : ℝ → Prop) (h : P (∫ x, S.indicator 1 x ∂μ)) : P (μ.real S) := by
  rw [← integral_indicator_one hS]
  exact h

/-! ### R33. `integral_finsetSum` · `(∀ i ∈ s, Integrable (f i) μ) → ∫ ∑ = ∑ ∫` · goal -/
example {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) (P : ℝ → Prop) (h : P (∑ i ∈ s, ∫ x, f i x ∂μ)) :
    P (∫ x, ∑ i ∈ s, f i x ∂μ) := by
  rw [integral_finsetSum s hf]
  exact h

/-! ### R34. `integral_const_mul` · `∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (f : Ω → ℝ) (P : ℝ → Prop)
    (h : P (c * ∫ x, f x ∂μ)) : P (∫ x, c * f x ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A case split on membership, then the indicator lemmas: `𝟙_S · 𝟙_S = 𝟙_S` (R1, R4, R8) -/
example {Ω : Type} (S : Set Ω) (x : Ω) :
    S.indicator (1 : Ω → ℝ) x * S.indicator 1 x = S.indicator 1 x := by
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem hx]
    simp

/-! ### W2. Split off the empty subset and put it in front (R17, then `add_comm`) -/
example {ι : Type} [DecidableEq ι] (s : Finset ι) (F : Finset ι → ℝ) :
    ∑ t ∈ s.powerset, F t = F ∅ + ∑ t ∈ s.powerset.erase ∅, F t := by
  rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]
  rw [add_comm]

/-! ### W3. Expected number of events that occur = sum of their measures (R33, R30, R29, R23, R32) -/
example {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι)
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    ∫ x, ∑ i ∈ s, (B i).indicator (1 : Ω → ℝ) x ∂μ = ∑ i ∈ s, μ.real (B i) := by
  rw [integral_finsetSum s]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_one (hB i)]
  · intro i _
    exact (integrable_const (1 : ℝ)).indicator (hB i)

/-! ### W4. A constant times an indicator (R34, R32) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (hS : MeasurableSet S) (c : ℝ) :
    ∫ x, c * S.indicator 1 x ∂μ = c * μ.real S := by
  rw [integral_const_mul]
  rw [integral_indicator_one hS]

end H052Guide

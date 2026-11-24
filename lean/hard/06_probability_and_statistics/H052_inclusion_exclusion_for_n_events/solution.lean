/- H052 | Inclusion–exclusion for n events | 1.5-2 h | indicators, Finset.prod_sub, powerset sums, integral_finsetSum, mathlib
GOAL
  `P(⋃_{i∈s} Aᵢ) = ∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) P(⋂_{i∈t} Aᵢ)` for a finite measure, from scratch: write
  `𝟙_{⋃} = 1 - ∏ (1 - 𝟙_{Aᵢ})`, expand the product over subsets, and integrate term by term.

REFERENCE
  `A.indicator f ω` is `f ω` if `ω ∈ A`, else `0`; with `(1 : Ω → ℝ)` it is the 0/1 indicator `𝟙_A`.  `μ.real A : ℝ` is `μ A` as a real.
  `s.powerset.filter (·.Nonempty)` (printed `s.powerset with t.Nonempty`): the nonempty `t ⊆ s`;  `t.card` is `|t|`.
  #check integral_indicator_one     -- MeasurableSet s → ∫ x, s.indicator 1 x ∂μ = μ.real s
  #check Finset.prod_sub            -- (f g s) : ∏ i ∈ s, (f i - g i) = ∑ t ∈ s.powerset, ((-1) ^ t.card * ∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i
  #check Finset.sum_filter          -- (p f) : ∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0
  #check Finset.sum_erase_add       -- (s f) : a ∈ s → ∑ x ∈ s.erase a, f x + f a = ∑ x ∈ s, f x   (with `Finset.empty_mem_powerset s`)
  #check Finset.prod_eq_zero        -- i ∈ s → f i = 0 → ∏ j ∈ s, f j = 0     (and `Finset.prod_eq_one : (∀ x ∈ s, f x = 1) → ∏ ... = 1`)
  #check Set.indicator_of_mem       -- a ∈ s → ∀ f, s.indicator f a = f a     (and `Set.indicator_of_notMem`: `a ∉ s → ... = 0`)
  #check integral_finsetSum         -- (s) : (∀ i ∈ s, Integrable (f i) μ) → ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ  (and `integral_const_mul`)
  #check Integrable.indicator       -- Integrable f μ → MeasurableSet s → Integrable (s.indicator f) μ   (start from `integrable_const 1`)
  #check Finset.measurableSet_biInter  -- (s) : (∀ b ∈ s, MeasurableSet (f b)) → MeasurableSet (⋂ b ∈ s, f b)   (and `_biUnion`)
BANNED: measureReal_biUnion_eq_sum_powerset, integral_biUnion_eq_sum_powerset, indicator_biUnion_eq_sum_powerset, prod_indicator_biUnion_sub_indicator, prod_indicator_biUnion_finset_sub_indicator, inclusion_exclusion_sum_biUnion, inclusion_exclusion_card_biUnion, exact?, apply?, rw?, hint, observe, try?
-/
import Mathlib

namespace H052

open MeasureTheory

-- MILESTONE (optional: change or delete)
theorem indicator_biUnion {Ω ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    (⋃ i ∈ s, A i).indicator (1 : Ω → ℝ) ω = 1 - ∏ i ∈ s, (1 - (A i).indicator 1 ω) := by
  by_cases h : ∃ i ∈ s, ω ∈ A i
  · obtain ⟨i, hi, hω⟩ := h
    rw [Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨i, hi, hω⟩), Finset.prod_eq_zero hi (by simp [hω])]
    simp
  · push Not at h
    rw [Set.indicator_of_notMem (by simpa using h),
      Finset.prod_eq_one (fun i hi => by simp [h i hi])]
    simp

-- MILESTONE (optional: change or delete)
theorem prod_indicator {Ω ι : Type*} (t : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    ∏ i ∈ t, (A i).indicator (1 : Ω → ℝ) ω = (⋂ i ∈ t, A i).indicator 1 ω := by
  by_cases h : ∀ i ∈ t, ω ∈ A i
  · rw [Set.indicator_of_mem (Set.mem_iInter₂.mpr h),
      Finset.prod_eq_one (fun i hi => by simp [h i hi])]
    simp
  · push Not at h
    obtain ⟨i, hi, hω⟩ := h
    rw [Finset.prod_eq_zero hi (by simp [hω]), Set.indicator_of_notMem]
    simp only [Set.mem_iInter, not_forall]
    exact ⟨i, hi, hω⟩

-- MILESTONE (optional: change or delete)
theorem indicator_expand {Ω ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    (⋃ i ∈ s, A i).indicator (1 : Ω → ℝ) ω =
      ∑ t ∈ s.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (t.card + 1) * (⋂ i ∈ t, A i).indicator 1 ω := by
  rw [indicator_biUnion, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, prod_indicator]
  -- WHY: split off the `t = ∅` term on both sides; on the left it is `1` and cancels `1 - _`.
  rw [Finset.sum_filter, ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s),
    ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]
  simp only [Finset.card_empty, pow_zero, one_mul, Finset.not_nonempty_empty, if_false, add_zero]
  have hI : (⋂ i ∈ (∅ : Finset ι), A i).indicator (1 : Ω → ℝ) ω = 1 := by simp
  rw [hI, sub_add_cancel_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
  rw [if_pos hne, pow_succ]
  ring

-- BEGIN SPEC
theorem inclusion_exclusion {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    [DecidableEq ι] (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    μ.real (⋃ i ∈ s, A i) =
      ∑ t ∈ s.powerset.filter (·.Nonempty), (-1 : ℝ) ^ (t.card + 1) * μ.real (⋂ i ∈ t, A i) :=
-- END SPEC
  by
    have hU : MeasurableSet (⋃ i ∈ s, A i) := Finset.measurableSet_biUnion s fun i _ => hA i
    have hI : ∀ t : Finset ι, MeasurableSet (⋂ i ∈ t, A i) :=
      fun t => Finset.measurableSet_biInter t fun i _ => hA i
    have hInt : ∀ t ∈ s.powerset.filter (·.Nonempty),
        Integrable (fun ω => (-1 : ℝ) ^ (t.card + 1) * (⋂ i ∈ t, A i).indicator 1 ω) μ :=
      fun t _ => ((integrable_const (1 : ℝ)).indicator (hI t)).const_mul _
    rw [← integral_indicator_one hU]
    simp_rw [indicator_expand s A]
    rw [integral_finsetSum _ hInt]
    exact Finset.sum_congr rfl fun t _ => by rw [integral_const_mul, integral_indicator_one (hI t)]

end H052

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work pointwise first. `ω` is outside the union iff every factor `1 - 𝟙_{Aᵢ}(ω)` is `1`; a product of indicators is the indicator of the intersection. Then integrate the pointwise identity.
H2. Milestones 1 and 2: `by_cases` on whether some `i ∈ s` has `ω ∈ A i` (resp. all `i ∈ t` do), then `Set.indicator_of_mem` / `indicator_of_notMem` with `Finset.prod_eq_zero` / `prod_eq_one`. Milestone 3: `rw [indicator_biUnion, Finset.prod_sub]` (with `f = 1`, `g = 𝟙_{Aᵢ}`), simplify `∏ 1 = 1`, apply `prod_indicator`, and split the `t = ∅` term off both sums with `Finset.sum_erase_add`; that term is `1` and cancels the leading `1 -`.
H3. Main: `rw [← integral_indicator_one hU]; simp_rw [indicator_expand s A]; rw [integral_finsetSum _ hInt]`, then `Finset.sum_congr rfl fun t _ => by rw [integral_const_mul, integral_indicator_one (hI t)]`, where `hInt` states integrability of `fun ω => (-1 : ℝ) ^ (t.card + 1) * (⋂ i ∈ t, A i).indicator 1 ω` via `(integrable_const (1 : ℝ)).indicator (hI t) |>.const_mul _`.
-/

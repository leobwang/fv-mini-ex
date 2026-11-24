/- H052 | Inclusion–exclusion for n events | 1.5-2 h | indicators, Finset.prod_sub, powerset sums, integral_finsetSum, mathlib
GOAL
  `P(⋃_{i∈s} Aᵢ) = ∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) P(⋂_{i∈t} Aᵢ)` for a finite measure, from scratch: write
  `𝟙_{⋃} = 1 - ∏ (1 - 𝟙_{Aᵢ})`, expand the product over subsets, and integrate term by term.

BANNED: measureReal_biUnion_eq_sum_powerset, integral_biUnion_eq_sum_powerset, indicator_biUnion_eq_sum_powerset, prod_indicator_biUnion_sub_indicator, prod_indicator_biUnion_finset_sub_indicator, inclusion_exclusion_sum_biUnion, inclusion_exclusion_card_biUnion, exact?, apply?, rw?, hint, observe, try?

GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H052

open MeasureTheory

/- SKELETON · indicator_biUnion   (milestone 1; prove it FIRST; indicator_expand rewrites with it)
  1. Case split on whether ω lies in some Aᵢ:  h : ∃ i ∈ s, ω ∈ A i                  R1
  2. Case yes. Unpack the witness i, hi, hω:                                           R2
       left: ω is in the union, so the indicator is `1 ω`; build the membership
       from the witness as a term:                                                     R4 with R3
       right: the factor at i is `1 - 1 = 0`, so the product is 0; the fact
       `1 - (A i).indicator 1 ω = 0` is a one-line `simp` using hω:                    R6
       finish the numbers (`1 ω` is 1):                                                simp (R5)
  3. Case no. Push the negation into h : ∀ i ∈ s, ω ∉ A i:                             R7
       left: ω is not in the union, so the indicator is 0; prove `ω ∉ ⋃ …` from h:    R8, R9
       right: every factor is `1 - 0 = 1`, so the product is 1 (each factor by
       `simp` using h):                                                                R10
       finish the numbers:                                                             simp
-/
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

/- SKELETON · prod_indicator   (milestone 2; indicator_expand uses it inside a sum, via R15)
  1. Case split on whether ω lies in every Aᵢ, i ∈ t:  h : ∀ i ∈ t, ω ∈ A i            R1
  2. Case yes. Right: ω is in the intersection (membership from h as a term), so the
     indicator is `1 ω`; left: every factor is 1 (`simp` using h), so the product is 1: R4 with R11, R10
       finish the numbers:                                                             simp (R5)
  3. Case no. Push the negation, unpack the witness i, hi, hω:                         R7, R2
       left: the factor at i is 0, so the product is 0:                                R6
       right: rewrite the indicator to 0 WITHOUT its argument; `rw` closes `0 = 0`
       and leaves the side goal `ω ∉ ⋂ i ∈ t, A i`:                                     R8
       turn the side goal into an `∃` and give the witness:                            R12
-/
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

/- SKELETON · indicator_expand   (milestone 3; uses milestones 1 and 2; inclusion_exclusion uses it)
  1. Rewrite the left side with milestone 1, then expand the product over subsets:    rw [indicator_biUnion], R13
  2. One `simp only`: drop `∏ 1` and `* 1`, and turn `∏ i ∈ t, 𝟙_{Aᵢ}` into
     `𝟙_{⋂ i ∈ t, Aᵢ}` with milestone 2 under the sum:                                 R14, R15
  3. Unfold the filter on the right (now both sides sum over `s.powerset`), then split
     off the `t = ∅` term from BOTH sums (the same rewrite, twice):                     R16, R17, R17
  4. Clean the ∅ terms in one `simp only` (also `add_zero`):                            R18, R19
     The ∅-intersection indicator is 1; prove it first as a fact:                      R20
       h∅ : (⋂ i ∈ (∅ : Finset ι), A i).indicator (1 : Ω → ℝ) ω = 1
  5. rw [h∅], cancel `1 - (S + 1)` to `-S`, move the minus inside the sum:              R21, R22
  6. Compare the sums over `s.powerset.erase ∅` term by term:                           R23
       get `t.Nonempty` from `ht : t ∈ s.powerset.erase ∅`:                             R24, R25
       resolve the `if`, expand `(-1) ^ (|t| + 1)`, finish:                             R26, R27, ring
-/
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

/- SKELETON · inclusion_exclusion
  0. Prove the milestones first, in order 1 → 2 → 3 (3 uses 1 and 2). Only milestone 3
     (indicator_expand) is used here, in step 3.
  1. Measurability facts, as `have`s:                                                  R28
       hU : MeasurableSet (⋃ i ∈ s, A i)
       hI : ∀ t : Finset ι, MeasurableSet (⋂ i ∈ t, A i)
  2. Integrability of every summand, as a `have` with its type written out:            R29 → R30 → R31
       hInt : ∀ t ∈ s.powerset.filter (·.Nonempty),
         Integrable (fun ω => (-1 : ℝ) ^ (t.card + 1) * (⋂ i ∈ t, A i).indicator 1 ω) μ
  3. Measure → integral of the indicator, then expand the integrand with milestone 3
     under the `∫` binder:                                                             R32 (←), R15
  4. Integral of the sum → sum of the integrals:                                       R33
  5. Term by term: pull out the constant, integral of an indicator → measure:          R23, R34, R32
-/
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
H1. Work pointwise, at one `ω`: `𝟙_{⋃ Aᵢ} = 1 - ∏ (1 - 𝟙_{Aᵢ})` (milestone 1), a product of indicators is
    the indicator of the intersection (milestone 2), and expanding `∏ (1 - xᵢ)` over subsets gives the
    alternating sum (milestone 3). Then integrate: `∫ 𝟙_B dμ = μ.real B`.
H2. Milestones 1 and 2: `by_cases` on membership, then `Set.indicator_of_mem` / `Set.indicator_of_notMem`
    on the indicator side and `Finset.prod_eq_zero` / `Finset.prod_eq_one` on the product side. Milestone 3:
    `rw [indicator_biUnion, Finset.prod_sub]`, `simp only [Finset.prod_const_one, mul_one, prod_indicator]`,
    then split the `t = ∅` term off both sums with `Finset.sum_erase_add`; it is `1` and cancels `1 - _`.
    Main: `rw [← integral_indicator_one hU]`, `simp_rw [indicator_expand s A]`, `integral_finsetSum`.
H3. Milestone 3, the split: `rw [Finset.sum_filter, ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s),
    ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]`. Main, after the three rewrites:
    `exact Finset.sum_congr rfl fun t _ => by rw [integral_const_mul, integral_indicator_one (hI t)]`, with
    `hInt` from `fun t _ => ((integrable_const (1 : ℝ)).indicator (hI t)).const_mul _`.
-/

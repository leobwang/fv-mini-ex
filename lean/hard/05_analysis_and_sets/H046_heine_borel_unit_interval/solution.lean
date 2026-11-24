/- H046 | Heine–Borel for [0, 1] | 1-1.5 h | open covers, sSup, Finset, Metric.isOpen_iff, mathlib
GOAL
  Every cover of `[0, 1]` by open sets `U i` has a finite subcover (indices in a `t : Finset ι`).
  Creep along the interval: let `s` be the sup of the `x ∈ [0, 1]` with `[0, x]` finitely covered;
  the open set around `s` pushes the covered part past `s` unless `s = 1`, and then `[0, 1]` is covered.

REFERENCE
  -- `⋃ i ∈ t, U i`: union over the indices in the finset `t`;  `Metric.ball x ε = {y | dist y x < ε}`
  #check Metric.isOpen_iff      -- IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s
  #check Metric.mem_ball        -- y ∈ ball x ε ↔ dist y x < ε
  #check Real.dist_eq           -- dist x y = |x - y|      (then `abs_lt : |a| < b ↔ -b < a ∧ a < b`)
  #check Set.mem_iUnion         -- x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i
  #check Set.mem_iUnion₂        -- x ∈ ⋃ i, ⋃ j, s i j ↔ ∃ i j, x ∈ s i j   (this is the shape of `⋃ i ∈ t, U i`)
  #check Finset.mem_insert      -- a ∈ insert b s ↔ a = b ∨ a ∈ s   (`Finset.mem_insert_self`, `Finset.mem_insert_of_mem`)
  #check le_csSup               -- BddAbove s → a ∈ s → a ≤ sSup s
  #check csSup_le               -- s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a
  #check exists_lt_of_lt_csSup  -- s.Nonempty → b < sSup s → ∃ a ∈ s, b < a
  #check min_choice             -- min a b = a ∨ min a b = b
  -- begin with `classical` (so `insert j t` can decide equality on `ι`); name the set with `set S : Set ℝ := {x | ...}`
NOTE: no compactness in any form (including the `CompactSpace` instance on the subtype `Icc 0 1`).
BANNED: IsCompact, IsSeqCompact.isCompact, CompactSpace, CompactIccSpace, ProperSpace, IsSeqCompact, IsCountablyCompact.isSeqCompact, isCompact_Icc, isCompact_uIcc, isCompact_closedBall, isCompact_range, isCompact_univ, isCompact_univ_iff, isCompact_iff_compactSpace, Metric.isCompact_of_isClosed_isBounded, Metric.isCompact_iff_isClosed_bounded, isCompact_iff_finite_subcover, isCompact_iff_isSeqCompact, Bornology.IsBounded.isCompact_closure, NormedSpace.isCompact_closure_of_isBounded, TotallyBounded.isCompact_of_isClosed, TotallyBounded.isCompact_of_isComplete, isCompact_iff_totallyBounded_isComplete, isCompact_iff_finite_subfamily_closed, isCompact_iff_ultrafilter_le_nhds, isCompact_iff_ultrafilter_le_nhds', IsCompact.elim_finite_subcover, IsCompact.elim_finite_subcover_image, IsCompact.elim_finite_subfamily_closed, IsCompact.elim_finite_subfamily_isClosed_subtype, IsCompact.elim_directed_cover, IsCompact.elim_directed_family_closed, IsCompact.elim_nhds_subcover, IsCompact.elim_nhds_subcover', IsCompact.elim_nhdsWithin_subcover, IsCompact.elim_nhdsWithin_subcover', IsCompact.finite_compact_cover, finite_cover_nhds, finite_cover_nhds_interior, lebesgue_number_lemma, lebesgue_number_lemma_of_metric, Filter.cocompact, Filter.cocompact_eq_bot, Filter.mem_cocompact, Filter.mem_cocompact', Filter.hasBasis_cocompact, Filter.coclosedCompact, compactSpace_Icc, compactSpace_of_completeLinearOrder, unitInterval, exists_clusterPt_of_compactSpace, isCompact_iff_isCompact_univ, Subtype.isCompact_iff, isCompact_diagonal, UniformSpace.isCompact_iff_isSeqCompact, SeqCompactSpace, CountablyCompactSpace, IsCountablyCompact, IsSeqCompact.isCountablyCompact, TotallyBounded, totallyBounded_Icc, Metric.totallyBounded_iff, IsCompact.elim_nhds_subcover_nhdsSet, IsCompact.elim_nhds_subcover_nhdsSet', IsCompact.inter_iInter_nonempty, IsCompact.nonempty_inter_sInter, CompactSpace.nonempty_sInter, CompactSpace.iInter_nonempty, IsCompact.ultrafilter_le_nhds, IsCompact.ultrafilter_le_nhds', IsCompact.induction_on, TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace, IsCompact.finite_cover_balls, finite_cover_balls_of_compact, exists_finite_cover_balls_of_isCompact_closure, Metric.exists_finite_isCover_of_isCompact, Metric.exists_finite_isCover_of_isCompact_closure, Metric.exists_finite_isCover_of_totallyBounded, Metric.finite_approx_of_totallyBounded, TopologicalSpace.Opens.IsBasis.exists_finite_of_isCompact, TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact, LocallyFinite.finite_nonempty_inter_compact, LocallyFinite.finite_nonempty_of_compact, LocallyFinite.finite_of_compact, exists_subset_iUnion_compact_subset_t2space, exists_subset_iUnion_closure_subset_t2space, IsCompact.sigma_exists_finite_sigma_eq, eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open, eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open, Metric.compactSpace_iff_isBounded_univ, Metric.sphere.compactSpace, lebesgue_number_lemma_sUnion, lebesgue_number_lemma_of_metric_sUnion, lebesgue_number_lemma_nhds, lebesgue_number_lemma_nhds', lebesgue_number_lemma_nhdsWithin, lebesgue_number_lemma_nhdsWithin', lebesgue_number_lemma_of_emetric, lebesgue_number_lemma_of_emetric_sUnion, lebesgue_number_lemma_of_emetric_nhds, lebesgue_number_lemma_of_emetric_nhds', lebesgue_number_lemma_of_emetric_nhdsWithin, lebesgue_number_lemma_of_emetric_nhdsWithin', lebesgue_number_of_compact_open, Set.image, Set.preimage, continuous_subtype_val, Continuous.subtype_val, isOpen_induced_iff, isOpen_induced, Subtype.range_coe, fun_prop, continuity, Set.Finite.isCompact_convexHull, isCompact_stdSimplex, Affine.Simplex.isCompact_closedInterior, Metric.exists_isCompact_closedBall, Metric.eventually_isCompact_closedBall, MontelSpace.isCompact_of_isClosed_of_isVonNBounded, Metric.isCompact_closure_iff_exists_finite_isCover, isCompact_closure_of_totallyBounded_quasiComplete, isCompact_closedAbsConvexHull_of_totallyBounded, Filter.TotallyBounded.isCompact_setOf_clusterPt, UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset, LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset, Convex.exists_subset_interior_convexHull_finset_of_isCompact, isCompact_closure_interUnionBalls
-/
import Mathlib

namespace H046

open Set

-- MILESTONE (optional: change or delete)
theorem zero_mem_S {ι : Type*} (U : ι → Set ℝ) (hcov : Icc 0 1 ⊆ ⋃ i, U i) :
    (0 : ℝ) ∈ {x | x ∈ Icc 0 1 ∧ ∃ t : Finset ι, Icc 0 x ⊆ ⋃ i ∈ t, U i} := by
  classical
  refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov ⟨le_rfl, zero_le_one⟩)
  refine ⟨{i}, fun z hz => ?_⟩
  have hz0 : z = 0 := le_antisymm hz.2 hz.1
  exact mem_iUnion₂.mpr ⟨i, Finset.mem_singleton_self i, hz0 ▸ hi⟩

-- MILESTONE (optional: change or delete)
theorem extend_cover {ι : Type*} [DecidableEq ι] (U : ι → Set ℝ) (x s ε : ℝ)
    (t : Finset ι) (j : ι) (ht : Icc 0 x ⊆ ⋃ i ∈ t, U i) (hball : Metric.ball s ε ⊆ U j)
    (hx : s - ε < x) : Icc 0 (min (s + ε / 2) 1) ⊆ ⋃ i ∈ insert j t, U i := by
  intro z hz
  by_cases hzx : z ≤ x
  · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (ht ⟨hz.1, hzx⟩)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hzi⟩
  · push Not at hzx
    refine mem_iUnion₂.mpr ⟨j, Finset.mem_insert_self j t, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.2.trans (min_le_left _ _)]

-- BEGIN SPEC
theorem heine_borel {ι : Type*} (U : ι → Set ℝ) (hU : ∀ i, IsOpen (U i))
    (hcov : Set.Icc 0 1 ⊆ ⋃ i, U i) : ∃ t : Finset ι, Set.Icc (0 : ℝ) 1 ⊆ ⋃ i ∈ t, U i :=
-- END SPEC
  by
    classical
    set S : Set ℝ := {x | x ∈ Icc 0 1 ∧ ∃ t : Finset ι, Icc 0 x ⊆ ⋃ i ∈ t, U i}
    have h0 : (0 : ℝ) ∈ S := zero_mem_S U hcov
    have hbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
    set s := sSup S
    have hs0 : 0 ≤ s := le_csSup hbdd h0
    have hs1 : s ≤ 1 := csSup_le ⟨0, h0⟩ fun x hx => hx.1.2
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov ⟨hs0, hs1⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU j) s hj
    obtain ⟨x, ⟨-, t, ht⟩, hx⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ (sub_lt_self s hε)
    set y := min (s + ε / 2) 1
    have hyS : y ∈ S :=
      ⟨⟨le_min (by linarith) zero_le_one, min_le_right _ _⟩, insert j t,
        extend_cover U x s ε t j ht hball hx⟩
    have hys : y ≤ s := le_csSup hbdd hyS
    -- WHY: `y ≤ s` rules out `y = s + ε / 2`, so the `min` must be `1`.
    have hy1 : y = 1 := by
      rcases min_choice (s + ε / 2) 1 with h | h
      · have : y = s + ε / 2 := h
        linarith
      · exact h
    obtain ⟨-, t', ht'⟩ := hyS
    exact ⟨t', hy1 ▸ ht'⟩

end H046

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Let `S = {x | x ∈ Icc 0 1 ∧ ∃ t : Finset ι, Icc 0 x ⊆ ⋃ i ∈ t, U i}` and `s = sSup S`. `S` contains `0` and is bounded by `1`, so `0 ≤ s ≤ 1`, and `s` lies in some `U j`, which contains a ball `ball s ε`.
H2. Some `x ∈ S` has `s - ε < x` (`exists_lt_of_lt_csSup`); add `j` to its finset. Then `y = min (s + ε / 2) 1` is in `S` (milestone `extend_cover`: points `z ≤ x` are covered by `t`, the others are within `ε` of `s`). So `y ≤ s`, which rules out `y = s + ε / 2`; by `min_choice`, `y = 1`.
H3. In `extend_cover`: `intro z hz; by_cases hzx : z ≤ x`; first case `obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (ht ⟨hz.1, hzx⟩)` and `exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hzi⟩`; second case `mem_iUnion₂.mpr ⟨j, Finset.mem_insert_self j t, hball _⟩` with `rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.2.trans (min_le_left _ _)]`.
-/

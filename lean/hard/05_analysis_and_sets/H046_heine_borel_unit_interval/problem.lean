/- H046 | Heine–Borel for [0, 1] | 1-1.5 h | open covers, sSup, Finset, Metric.isOpen_iff, mathlib
GOAL
  Every cover of `[0, 1]` by open sets `U i` has a finite subcover (indices in a `t : Finset ι`).
  Creep along the interval: let `s` be the sup of the `x ∈ [0, 1]` with `[0, x]` finitely covered;
  the open set around `s` pushes the covered part past `s` unless `s = 1`, and then `[0, 1]` is covered.
BANNED: IsCompact, IsSeqCompact.isCompact, CompactSpace, CompactIccSpace, ProperSpace, IsSeqCompact, IsCountablyCompact.isSeqCompact, isCompact_Icc, isCompact_uIcc, isCompact_closedBall, isCompact_range, isCompact_univ, isCompact_univ_iff, isCompact_iff_compactSpace, Metric.isCompact_of_isClosed_isBounded, Metric.isCompact_iff_isClosed_bounded, isCompact_iff_finite_subcover, isCompact_iff_isSeqCompact, Bornology.IsBounded.isCompact_closure, NormedSpace.isCompact_closure_of_isBounded, TotallyBounded.isCompact_of_isClosed, TotallyBounded.isCompact_of_isComplete, isCompact_iff_totallyBounded_isComplete, isCompact_iff_finite_subfamily_closed, isCompact_iff_ultrafilter_le_nhds, isCompact_iff_ultrafilter_le_nhds', IsCompact.elim_finite_subcover, IsCompact.elim_finite_subcover_image, IsCompact.elim_finite_subfamily_closed, IsCompact.elim_finite_subfamily_isClosed_subtype, IsCompact.elim_directed_cover, IsCompact.elim_directed_family_closed, IsCompact.elim_nhds_subcover, IsCompact.elim_nhds_subcover', IsCompact.elim_nhdsWithin_subcover, IsCompact.elim_nhdsWithin_subcover', IsCompact.finite_compact_cover, finite_cover_nhds, finite_cover_nhds_interior, lebesgue_number_lemma, lebesgue_number_lemma_of_metric, Filter.cocompact, Filter.cocompact_eq_bot, Filter.mem_cocompact, Filter.mem_cocompact', Filter.hasBasis_cocompact, Filter.coclosedCompact, compactSpace_Icc, compactSpace_of_completeLinearOrder, unitInterval, exists_clusterPt_of_compactSpace, isCompact_iff_isCompact_univ, Subtype.isCompact_iff, isCompact_diagonal, UniformSpace.isCompact_iff_isSeqCompact, SeqCompactSpace, CountablyCompactSpace, IsCountablyCompact, IsSeqCompact.isCountablyCompact, TotallyBounded, totallyBounded_Icc, Metric.totallyBounded_iff, IsCompact.elim_nhds_subcover_nhdsSet, IsCompact.elim_nhds_subcover_nhdsSet', IsCompact.inter_iInter_nonempty, IsCompact.nonempty_inter_sInter, CompactSpace.nonempty_sInter, CompactSpace.iInter_nonempty, IsCompact.ultrafilter_le_nhds, IsCompact.ultrafilter_le_nhds', IsCompact.induction_on, TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace, IsCompact.finite_cover_balls, finite_cover_balls_of_compact, exists_finite_cover_balls_of_isCompact_closure, Metric.exists_finite_isCover_of_isCompact, Metric.exists_finite_isCover_of_isCompact_closure, Metric.exists_finite_isCover_of_totallyBounded, Metric.finite_approx_of_totallyBounded, TopologicalSpace.Opens.IsBasis.exists_finite_of_isCompact, TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact, LocallyFinite.finite_nonempty_inter_compact, LocallyFinite.finite_nonempty_of_compact, LocallyFinite.finite_of_compact, exists_subset_iUnion_compact_subset_t2space, exists_subset_iUnion_closure_subset_t2space, IsCompact.sigma_exists_finite_sigma_eq, eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open, eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open, Metric.compactSpace_iff_isBounded_univ, Metric.sphere.compactSpace, lebesgue_number_lemma_sUnion, lebesgue_number_lemma_of_metric_sUnion, lebesgue_number_lemma_nhds, lebesgue_number_lemma_nhds', lebesgue_number_lemma_nhdsWithin, lebesgue_number_lemma_nhdsWithin', lebesgue_number_lemma_of_emetric, lebesgue_number_lemma_of_emetric_sUnion, lebesgue_number_lemma_of_emetric_nhds, lebesgue_number_lemma_of_emetric_nhds', lebesgue_number_lemma_of_emetric_nhdsWithin, lebesgue_number_lemma_of_emetric_nhdsWithin', lebesgue_number_of_compact_open, Set.image, Set.preimage, continuous_subtype_val, Continuous.subtype_val, isOpen_induced_iff, isOpen_induced, Subtype.range_coe, fun_prop, continuity, Set.Finite.isCompact_convexHull, isCompact_stdSimplex, Affine.Simplex.isCompact_closedInterior, Metric.exists_isCompact_closedBall, Metric.eventually_isCompact_closedBall, MontelSpace.isCompact_of_isClosed_of_isVonNBounded, Metric.isCompact_closure_iff_exists_finite_isCover, isCompact_closure_of_totallyBounded_quasiComplete, isCompact_closedAbsConvexHull_of_totallyBounded, Filter.TotallyBounded.isCompact_setOf_clusterPt, UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset, LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset, Convex.exists_subset_interior_convexHull_finset_of_isCompact, isCompact_closure_interUnionBalls

GUIDE
  Entries R1–R35: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H046

open Set

/- SKELETON · zero_mem_S   (milestone; prove it FIRST: heine_borel needs `0 ∈ S` for every sSup lemma)
  1. The membership is a pair: give `0 ∈ Icc 0 1` now, leave the finset part:    R6 with R3, R4, R5
  2. `0` lies in some `U i`: apply hcov to `0 ∈ Icc 0 1`, then name the index:     R7 → R8
  3. Give the finset `{i}` and open the subset (a point z, hz : z ∈ Icc 0 0):     R9
  4. hz0 : z = 0 from the two halves of hz:                                       R10 with R3
  5. Into the union over `{i}`: the index i, its membership in `{i}`, and
     hi moved along hz0:                                                         R11, R12, R13
-/
-- MILESTONE (optional: change or delete)
theorem zero_mem_S {ι : Type*} (U : ι → Set ℝ) (hcov : Icc 0 1 ⊆ ⋃ i, U i) :
    (0 : ℝ) ∈ {x | x ∈ Icc 0 1 ∧ ∃ t : Finset ι, Icc 0 x ⊆ ⋃ i ∈ t, U i} := by
  sorry

/- SKELETON · extend_cover   (milestone; heine_borel uses it to show `min (s + ε / 2) 1 ∈ S`)
  1. Open the subset: a point z, hz : z ∈ Icc 0 (min (s + ε / 2) 1):             R9
  2. Split on hzx : z ≤ x:                                                        R14
  3. z ≤ x: ht covers z (apply it to ⟨hz.1, hzx⟩); take that union apart, and
     put the same index back into the bigger finset:                             R7, R11 → R15, R11
  4. ¬ z ≤ x: first make hzx : x < z:                                             R16
     the index j, its membership in insert j t, and hball applied to a goal:     R11, R17, R7
     ball → two inequalities; split them; each follows from hx, hzx and
     z ≤ s + ε / 2 (hz.2 chained with min_le_left):                              R18 → R19 → R20,
                                                                                 constructor, R24 with R23, R21
-/
-- MILESTONE (optional: change or delete)
theorem extend_cover {ι : Type*} [DecidableEq ι] (U : ι → Set ℝ) (x s ε : ℝ)
    (t : Finset ι) (j : ι) (ht : Icc 0 x ⊆ ⋃ i ∈ t, U i) (hball : Metric.ball s ε ⊆ U j)
    (hx : s - ε < x) : Icc 0 (min (s + ε / 2) 1) ⊆ ⋃ i ∈ insert j t, U i := by
  sorry

/- SKELETON · heine_borel
  0. Prove the milestones zero_mem_S and extend_cover first (used in steps 2 and 6).
  1. `classical` (extend_cover needs DecidableEq ι), then name
       S := {x | x ∈ Icc 0 1 ∧ ∃ t : Finset ι, Icc 0 x ⊆ ⋃ i ∈ t, U i}:            R1, R25
  2. h0 : 0 ∈ S (zero_mem_S); hbdd : BddAbove S with bound 1:                     R26 with R3
  3. Name s := sSup S; hs0 : 0 ≤ s and hs1 : s ≤ 1:                               R25, R27, R28
  4. s lies in some U j (hcov at ⟨hs0, hs1⟩); U j is open, so
       ε, hε, hball : Metric.ball s ε ⊆ U j:                                      R7 → R8, R29
  5. Some x ∈ S beats s - ε; keep its finset t and ht, drop the Icc part:        R30 with R31, R32
  6. Name y := min (s + ε / 2) 1 (R25) and prove hyS : y ∈ S:
       y ∈ Icc 0 1                                                               R6, R33 with R24, R5, R22
       the finset insert j t covers Icc 0 y                                      extend_cover
     then hys : y ≤ s:                                                           R27
  7. hy1 : y = 1: split on which side the min is; in the case
     y = s + ε / 2, hys and hε contradict:                                       R34, R35, R24
  8. Take the finset out of hyS and move its cover along hy1:                    R32, R13
-/
-- BEGIN SPEC
theorem heine_borel {ι : Type*} (U : ι → Set ℝ) (hU : ∀ i, IsOpen (U i))
    (hcov : Set.Icc 0 1 ⊆ ⋃ i, U i) : ∃ t : Finset ι, Set.Icc (0 : ℝ) 1 ⊆ ⋃ i ∈ t, U i :=
-- END SPEC
  sorry

end H046

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the two milestones first. The main proof is the "creeping" argument: with
    `S = {x | x ∈ Icc 0 1 ∧ ∃ t : Finset ι, Icc 0 x ⊆ ⋃ i ∈ t, U i}` and `s = sSup S`, the open set
    `U j` containing `s` covers a ball around `s`, which pushes the covered part past `s` unless the
    push is capped at `1`. Every `sSup` lemma needs `0 ∈ S` (zero_mem_S) and `BddAbove S`.
H2. zero_mem_S: an index `i` with `0 ∈ U i` from `hcov` (R7, R8), the finset `{i}`, and `z = 0` for
    `z ∈ Icc 0 0`. extend_cover: `by_cases hzx : z ≤ x`; `t` covers the left part, `U j` (through
    `hball`) the right part. heine_borel: `0 ≤ s ≤ 1` (le_csSup, csSup_le), `s ∈ U j`,
    `Metric.isOpen_iff` gives `ε`, `exists_lt_of_lt_csSup` with `sub_lt_self` gives `x ∈ S` above
    `s - ε`; then `y = min (s + ε / 2) 1 ∈ S` by extend_cover, so `y ≤ s`, and `min_choice` forces `y = 1`.
H3. extend_cover, first case: `obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (ht ⟨hz.1, hzx⟩)` and
    `exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hzi⟩`; second case:
    `refine mem_iUnion₂.mpr ⟨j, Finset.mem_insert_self j t, hball ?_⟩`, then
    `rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.2.trans (min_le_left _ _)]`.
    heine_borel: `obtain ⟨x, ⟨-, t, ht⟩, hx⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ (sub_lt_self s hε)` and
    `hyS : y ∈ S := ⟨⟨le_min (by linarith) zero_le_one, min_le_right _ _⟩, insert j t, extend_cover U x s ε t j ht hball hx⟩`.
-/

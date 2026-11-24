/- H041 | Intermediate value theorem | 45-75 min | sSup, completeness, epsilon-delta, by_contra, mathlib
GOAL
  If `f : ℝ → ℝ` is continuous (ε-δ, as `ContAt` below), `a ≤ b` and `f a ≤ 0 ≤ f b`, then `f` has a zero in
  `[a, b]` (`Set.Icc a b`). Take `c = sSup {x ∈ [a, b] | f x ≤ 0}` and rule out `f c > 0` and `f c < 0`.
  (`sSup S` is the least upper bound of `S : Set ℝ`; its lemmas need `S.Nonempty` and/or `BddAbove S`.)
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto, nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, EMetric
BANNED: intermediate_value_Icc, intermediate_value_Icc', intermediate_value_univ, intermediate_value_univ₂, intermediate_value_uIcc, intermediate_value_Ioo, intermediate_value_Ico, intermediate_value_Ioc, mem_range_of_exists_le_of_exists_ge, IsPreconnected.intermediate_value, IsPreconnected.intermediate_value₂, IsPreconnected, isPreconnected_Icc, isConnected_Icc, ContinuousOn.surjOn_Icc, ContinuousOn.image_Icc, intermediate_value_Ico', intermediate_value_Ioc', intermediate_value_Ioo', intermediate_value_Ici, intermediate_value_Ici', intermediate_value_Iic, intermediate_value_Iic', intermediate_value_Ioi, intermediate_value_Ioi', intermediate_value_Iio, intermediate_value_Iio', IsPreconnected.intermediate_value_Iii, intermediate_value_univ₂_eventually₁, intermediate_value_univ₂_eventually₂, IsPreconnected.intermediate_value₂_eventually₁, IsPreconnected.intermediate_value₂_eventually₂, ContinuousOn.surjOn_uIcc, ContinuousOn.surjOn_of_tendsto, ContinuousOn.surjOn_of_tendsto', IsPreconnected.Icc_subset, IsPreconnected.ordConnected, IsPreconnected.mem_intervals, exists_mem_Icc_isFixedPt, exists_mem_uIcc_isFixedPt, exists_mem_Icc_isFixedPt_of_mapsTo, exists_mem_uIcc_isFixedPt_of_mapsTo, exists_mem_Icc_isFixedPt_of_surjOn, exists_mem_uIcc_isFixedPt_of_surjOn, IsConnected.Ioo_csInf_csSup_subset, eq_Icc_csInf_csSup_of_connected_bdd_closed
BANNED: CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop, tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def, cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, Metric.continuous_iff, Metric.continuousAt_iff, Filter.HasBasis, HasBasis.tendsto_iff, HasBasis.tendsto_left_iff, HasBasis.tendsto_right_iff, nhds_basis_abs_sub_lt, nhds_basis_Ioo_pos, nhds_basis_Ioo, nhds_basis_Ioo', mem_nhds_iff_exists_Ioo_subset, Ioo_mem_nhds, nhdsWithin_le_nhds, mem_nhds_iff_exists_Ioo_subset', mem_nhdsWithin_of_mem_nhds, isOpen_Ioo
BANNED: fun_prop, continuity, exact?, apply?, try?, hint

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H041

-- BEGIN SPEC
def ContAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε
-- END SPEC

/- SKELETON · sup_bounds   (milestone; prove it FIRST: f_sup_ge and ivt use it)
  1. Split the `∧`:                                                         constructor
  2. a ≤ sSup S: the element bound, with the side condition `BddAbove S`
     built from hS:                                                         R3 with R1
  3. sSup S ≤ b: the least-bound property, with `S.Nonempty` built from ha:  R4 with R2
-/
-- MILESTONE (optional: change or delete)
theorem sup_bounds (S : Set ℝ) (a b : ℝ) (ha : a ∈ S) (hS : ∀ x ∈ S, x ≤ b) :
    a ≤ sSup S ∧ sSup S ≤ b := by
  exact ⟨le_csSup ⟨b, hS⟩ ha, csSup_le ⟨a, ha⟩ hS⟩

/- SKELETON · f_sup_le   (milestone: the case f c > 0 is impossible; ivt uses it)
  1. Name the set: set S : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x ≤ 0}          R5
  2. Facts, as `have`s:  haS : a ∈ S                                         R6 (R7 for a ≤ a)
                         hbdd : BddAbove S, bound b, proof fun x hx => hx.1.2 R1, R8
  3. Name the supremum: set c := sSup S                                      R5
  4. Suppose not, and turn ¬(f c ≤ 0) into hpos : 0 < f c:                   R9, R10
  5. ε := f c gives δ, hδ, hd:                                               R11
  6. Some s ∈ S has c - δ < s (side conditions: R2 from haS, R12 from hδ):  R13
     and s ≤ c:                                                              R3 with hbdd
  7. Feed s to hd; its premise |s - c| < δ:                                  R14, constructor <;> R16
  8. Open the result and add f s ≤ 0 (= hsS.2):                              R15, R16 with R8
-/
-- MILESTONE (optional: change or delete)
theorem f_sup_le (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ∀ x, ContAt f x) (ha : f a ≤ 0) :
    f (sSup {x | x ∈ Set.Icc a b ∧ f x ≤ 0}) ≤ 0 := by
  set S : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x ≤ 0}
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, ha⟩
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  set c := sSup S
  by_contra hpos
  push Not at hpos
  obtain ⟨δ, hδ, hd⟩ := hf c (f c) hpos
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩ (sub_lt_self c hδ)
  have hsc : s ≤ c := le_csSup hbdd hsS
  have := hd s (by rw [abs_lt]; constructor <;> linarith)
  rw [abs_lt] at this
  linarith [hsS.2]

/- SKELETON · f_sup_ge   (milestone: the case f c < 0 is impossible; uses sup_bounds; ivt uses it)
  1. As in f_sup_le: set S, haS, then (before naming c)
     obtain ⟨hac, hcb⟩ from sup_bounds S a b haS (fun x hx => hx.1.2), and hbdd: R5, R6, R7, R8, R1
  2. set c := sSup S; suppose not, hneg : f c < 0:                           R5, R9, R10
  3. hcb' : c < b from hcb; in the branch h : c = b, put b into hneg and
     contradict hb:                                                          R17, R18, R16
  4. ε := -f c (its positivity by R16) gives δ, hδ, hd:                      R11
  5. The point: set y := min (c + δ / 2) b                                   R5
       hy1 : c < y                                                           R19 (R16, hcb')
       hy2 : y ≤ c + δ / 2                                                   R20
  6. hyS : y ∈ S, three goals:                                               R6
       a ≤ y: R16;   y ≤ b: R21;   f y ≤ 0: hd y via R14, constructor <;> R16, then R15, R16
  7. y ≤ c contradicts hy1:                                                  R3, R16
-/
-- MILESTONE (optional: change or delete)
theorem f_sup_ge (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ∀ x, ContAt f x) (ha : f a ≤ 0)
    (hb : 0 ≤ f b) : 0 ≤ f (sSup {x | x ∈ Set.Icc a b ∧ f x ≤ 0}) := by
  set S : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x ≤ 0}
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, ha⟩
  obtain ⟨hac, hcb⟩ := sup_bounds S a b haS (fun x hx => hx.1.2)
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  set c := sSup S
  by_contra hneg
  push Not at hneg
  -- WHY: `c` is a `set` variable, so `rintro rfl` would fail; argue `c ≠ b` by rewriting instead.
  have hcb' : c < b := lt_of_le_of_ne hcb (fun h => by rw [h] at hneg; linarith)
  obtain ⟨δ, hδ, hd⟩ := hf c (-f c) (by linarith)
  set y := min (c + δ / 2) b
  have hy1 : c < y := lt_min (by linarith) hcb'
  have hy2 : y ≤ c + δ / 2 := min_le_left _ _
  have hyS : y ∈ S := by
    refine ⟨⟨by linarith, min_le_right _ _⟩, ?_⟩
    have := hd y (by rw [abs_lt]; constructor <;> linarith)
    rw [abs_lt] at this
    linarith
  have := le_csSup hbdd hyS
  linarith

/- SKELETON · ivt
  0. Prove the three milestones first; this proof only assembles them.
  1. c := sSup {x | x ∈ Set.Icc a b ∧ f x ≤ 0} lies in [a, b]:
     obtain ⟨hac, hcb⟩ from sup_bounds; a ∈ S by R6 (R7), the bound by R8
  2. One `refine`: witness `_`, the interval proof as the TERM ⟨hac, hcb⟩ (it
     fixes the witness; with ⟨?_, ?_⟩ there Lean cannot find it), goal ?_:   R23
  3. f c = 0 from f_sup_le and f_sup_ge:                                     R22
-/
-- BEGIN SPEC
theorem ivt (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ∀ x, ContAt f x) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ c ∈ Set.Icc a b, f c = 0 :=
-- END SPEC
  by
    obtain ⟨hac, hcb⟩ := sup_bounds {x | x ∈ Set.Icc a b ∧ f x ≤ 0} a b ⟨⟨le_rfl, hab⟩, ha⟩
      (fun x hx => hx.1.2)
    exact ⟨_, ⟨hac, hcb⟩, le_antisymm (f_sup_le f a b hab hf ha) (f_sup_ge f a b hab hf ha hb)⟩

end H041

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `S = {x | x ∈ Set.Icc a b ∧ f x ≤ 0}` contains `a` (R6, R7) and is bounded above by `b` (R1, R8), so
    `c = sSup S` lies in `[a, b]` (sup_bounds: R3, R4). Show `f c ≤ 0` and `0 ≤ f c` separately, each by
    contradiction (R9, R10), and finish with `le_antisymm` (R22, R23).
H2. If `f c > 0`: `hf c (f c) hpos` gives `δ` (R11); `exists_lt_of_lt_csSup` with `sub_lt_self` gives `s ∈ S`
    with `c - δ < s ≤ c` (R12, R13, R3), so `f s > 0` by `abs_lt` and `linarith` (R14–R16). If `f c < 0`: first
    `c < b` (R17, R18, as `0 ≤ f b`); with `ε = -f c`, the point `y = min (c + δ / 2) b` (R19–R21) is in `S`
    but `y > c`, contradicting `le_csSup`.
H3. `obtain ⟨δ, hδ, hd⟩ := hf c (f c) hpos`, `obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩
    (sub_lt_self c hδ)`, then `have := hd s (by rw [abs_lt]; constructor <;> linarith)` and
    `rw [abs_lt] at this; linarith [hsS.2]`. Avoid `rintro rfl` on a `set` variable; prove `c < b` with
    `lt_of_le_of_ne hcb (fun h => by rw [h] at hneg; linarith)`.
-/

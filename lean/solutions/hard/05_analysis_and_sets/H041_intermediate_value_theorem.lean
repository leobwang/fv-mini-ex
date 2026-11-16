/- H041 | Intermediate value theorem | 45-75 min | sSup, completeness, epsilon-delta, by_contra, mathlib
GOAL
  If `f : ℝ → ℝ` is continuous (ε-δ, as `ContAt` below), `a ≤ b` and `f a ≤ 0 ≤ f b`, then `f` has a zero in
  `[a, b]` (`Set.Icc a b`). Take `c = sSup {x ∈ [a, b] | f x ≤ 0}` and rule out `f c > 0` and `f c < 0`.
  (`sSup S` is the least upper bound of `S : Set ℝ`; its lemmas need `S.Nonempty` and/or `BddAbove S`.)

REFERENCE
  #check le_csSup                -- BddAbove s → a ∈ s → a ≤ sSup s
  #check csSup_le                -- s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a
  #check exists_lt_of_lt_csSup   -- s.Nonempty → b < sSup s → ∃ a ∈ s, b < a
  example (S : Set ℝ) (b : ℝ) (h : ∀ x ∈ S, x ≤ b) : BddAbove S := ⟨b, h⟩
  example (S : Set ℝ) (a : ℝ) (h : a ∈ S) : S.Nonempty := ⟨a, h⟩
  #check abs_lt                  -- |a| < b ↔ -b < a ∧ a < b
  #check lt_min                  -- a < b → a < c → a < min b c   (and `min_le_left a b : min a b ≤ a`)
  -- `set c := sSup S with hc` names a term;  `by_contra h; push Not at h` turns `¬ (x ≤ y)` into `y < x`
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto, nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, EMetric
BANNED: intermediate_value_Icc, intermediate_value_Icc', intermediate_value_univ, intermediate_value_univ₂, intermediate_value_uIcc, intermediate_value_Ioo, intermediate_value_Ico, intermediate_value_Ioc, mem_range_of_exists_le_of_exists_ge, IsPreconnected.intermediate_value, IsPreconnected.intermediate_value₂, IsPreconnected, isPreconnected_Icc, isConnected_Icc, ContinuousOn.surjOn_Icc, ContinuousOn.image_Icc, intermediate_value_Ico', intermediate_value_Ioc', intermediate_value_Ioo', intermediate_value_Ici, intermediate_value_Ici', intermediate_value_Iic, intermediate_value_Iic', intermediate_value_Ioi, intermediate_value_Ioi', intermediate_value_Iio, intermediate_value_Iio', IsPreconnected.intermediate_value_Iii, intermediate_value_univ₂_eventually₁, intermediate_value_univ₂_eventually₂, IsPreconnected.intermediate_value₂_eventually₁, IsPreconnected.intermediate_value₂_eventually₂, ContinuousOn.surjOn_uIcc, ContinuousOn.surjOn_of_tendsto, ContinuousOn.surjOn_of_tendsto', IsPreconnected.Icc_subset, IsPreconnected.ordConnected, IsPreconnected.mem_intervals, exists_mem_Icc_isFixedPt, exists_mem_uIcc_isFixedPt, exists_mem_Icc_isFixedPt_of_mapsTo, exists_mem_uIcc_isFixedPt_of_mapsTo, exists_mem_Icc_isFixedPt_of_surjOn, exists_mem_uIcc_isFixedPt_of_surjOn, IsConnected.Ioo_csInf_csSup_subset, eq_Icc_csInf_csSup_of_connected_bdd_closed
BANNED: CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop, tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def, cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, Metric.continuous_iff, Metric.continuousAt_iff, Filter.HasBasis, HasBasis.tendsto_iff, HasBasis.tendsto_left_iff, HasBasis.tendsto_right_iff, nhds_basis_abs_sub_lt, nhds_basis_Ioo_pos, nhds_basis_Ioo, nhds_basis_Ioo', mem_nhds_iff_exists_Ioo_subset, Ioo_mem_nhds, nhdsWithin_le_nhds, mem_nhds_iff_exists_Ioo_subset', mem_nhdsWithin_of_mem_nhds, isOpen_Ioo
BANNED: fun_prop, continuity, exact?, apply?, try?, hint
NOTE: continuity is the custom `ContAt`; Mathlib's `Continuous`/filters (and `fun_prop`) are banned, so no bridge.
  The long BANNED list only closes bridges and IVT variants; the REFERENCE lemmas are all you need.
-/
import Mathlib

namespace H041

-- BEGIN SPEC
def ContAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem sup_bounds (S : Set ℝ) (a b : ℝ) (ha : a ∈ S) (hS : ∀ x ∈ S, x ≤ b) :
    a ≤ sSup S ∧ sSup S ≤ b := by
  exact ⟨le_csSup ⟨b, hS⟩ ha, csSup_le ⟨a, ha⟩ hS⟩

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
H1. `S = {x | x ∈ Set.Icc a b ∧ f x ≤ 0}` contains `a` and is bounded above by `b`, so `c = sSup S` lies in `[a, b]`. Show `f c ≤ 0` and `0 ≤ f c` separately, each by contradiction, and finish with `le_antisymm`.
H2. If `f c > 0`: continuity with `ε = f c` gives `δ`; `exists_lt_of_lt_csSup` gives `s ∈ S` with `c - δ < s ≤ c`, so `f s > 0`. If `f c < 0`: then `c < b` (as `0 ≤ f b`); with `ε = -f c`, the point `y = min (c + δ / 2) b` is in `S` but `y > c`.
H3. `obtain ⟨δ, hδ, hd⟩ := hf c (f c) hpos`, `obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩ (sub_lt_self c hδ)`, then `have := hd s (by rw [abs_lt]; constructor <;> linarith)` and `rw [abs_lt] at this; linarith [hsS.2]`. Avoid `rintro rfl` on a `set` variable; prove `c < b` with `lt_of_le_of_ne`.
-/

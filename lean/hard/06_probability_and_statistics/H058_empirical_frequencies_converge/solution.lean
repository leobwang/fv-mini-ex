/- H058 | Empirical frequencies converge | 1-1.5 h | strong law of large numbers, empirical CDF, indicators, IdentDistrib, ae_all_iff, a.e. filters, filter_upwards, order topology, mathlib
GOAL
  For i.i.d. real samples `X i` (pairwise independent, same law as `X 0`), almost surely the empirical CDF
  `Fₙ(t) = #{i < n | X i ≤ t} / n` tends to the CDF `F(t) = P(X 0 ≤ t)` at every `t` where `F` is continuous, all `t`
  at once. Strong law for one event; `ae_all_iff` over rational `t`; then squeeze `Fₙ(q) ≤ Fₙ(t) ≤ Fₙ(q')`, `q < t < q'`.

GUIDE
  Entries R1–R36: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H058

open MeasureTheory ProbabilityTheory Filter Topology

/- SKELETON · frequency_tendsto   (milestone 1: the strong law for one event)
  1. Name the indicator and the new sequence:                                R1
       f : α → ℝ := A.indicator (fun _ => 1)      Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  2. hf : Measurable f                                                       R2
  3. The three hypotheses of `strong_law_ae` for Y:
       hint : Integrable (Y 0) μ     bound C = 1:                            R3, R4, R5 → R6 → R7 → R8, R9
       hind : Pairwise fun i j => Y i ⟂ᵢ[μ] Y j                              R10, R11
       hid  : ∀ i, IdentDistrib (Y i) (Y 0) μ μ                              R12
  4. hmean : ∫ ω, Y 0 ω ∂μ = μ.real (X 0 ⁻¹' A)
       restate Y 0 as the indicator of X 0 ⁻¹' A, then integrate:            R13, R14 → R15
  5. The strong law for Y, pointwise in ω; put hmean into it:                R16, R17, R18
  6. Match the two sequences term by term:                                   R19
       hs : ∑ i ∈ Finset.range n, Y i ω = ↑{i ∈ Finset.range n | X i ω ∈ A}.card    R7, R20
       then rewrite the smul, hs, the division:                              R15, rw [hs], R21
-/
-- MILESTONE (optional: change or delete)
theorem frequency_tendsto {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → α) (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (A : Set α) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((Finset.range n).filter (fun i => X i ω ∈ A)).card / (n : ℝ))
      atTop (𝓝 (μ.real (X 0 ⁻¹' A))) := by
  set f : α → ℝ := A.indicator (fun _ => 1) with hf_def
  have hf : Measurable f := measurable_const.indicator hA
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i with hY
  have hint : Integrable (Y 0) μ := by
    refine Integrable.of_bound (hf.comp (hmeas 0)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    simp only [hY, hf_def, Function.comp, Set.indicator]
    split_ifs <;> simp
  have hind : Pairwise fun i j => Y i ⟂ᵢ[μ] Y j := fun i j hij => (hindep hij).comp hf hf
  have hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i => (hident i).comp hf
  have hmean : ∫ ω, Y 0 ω ∂μ = μ.real (X 0 ⁻¹' A) := by
    have e : Y 0 = (X 0 ⁻¹' A).indicator (fun _ => 1) := rfl
    rw [e, integral_indicator_const _ (hmeas 0 hA), smul_eq_mul, mul_one]
  filter_upwards [strong_law_ae Y hint hind hid] with ω hω
  rw [hmean] at hω
  convert hω using 2 with n
  have hs : ∑ i ∈ Finset.range n, Y i ω = ((Finset.range n).filter (fun i => X i ω ∈ A)).card := by
    simp only [hY, hf_def, Function.comp, Set.indicator]
    exact Finset.sum_boole _ _
  rw [smul_eq_mul, hs, div_eq_inv_mul]

/- SKELETON · frequency_tendsto_rat   (milestone 2; uses milestone 1)
  1. Swap "almost surely" and "for all rationals" (ℚ is countable):          R22, then intro q
  2. Milestone 1 with A = Set.Iic (q : ℝ): `exact` sees that {ω | X 0 ω ≤ ↑q}
     is X 0 ⁻¹' Set.Iic ↑q by definition; the set is measurable:            R23, R24
-/
-- MILESTONE (optional: change or delete)
theorem frequency_tendsto_rat {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ,
      Tendsto (fun n : ℕ => ((Finset.range n).filter (fun i => X i ω ≤ q)).card / (n : ℝ))
        atTop (𝓝 (μ.real {ω | X 0 ω ≤ q})) := by
  rw [ae_all_iff]
  intro q
  exact frequency_tendsto μ X hmeas hindep hident (Set.Iic (q : ℝ)) measurableSet_Iic

/- SKELETON · frequency_mono   (milestone 3)
  1. One call goes through the division, the cast, `card` and `filter`; what is left,
     X i ω ≤ s → X i ω ≤ t, it closes from hst itself:                       R25, R26
-/
-- MILESTONE (optional: change or delete)
theorem frequency_mono {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) {s t : ℝ} (hst : s ≤ t) :
    ((Finset.range n).filter (fun i => X i ω ≤ s)).card / (n : ℝ)
      ≤ ((Finset.range n).filter (fun i => X i ω ≤ t)).card / (n : ℝ) := by
  gcongr

/- SKELETON · empirical_cdf
  Prove the milestones first: frequency_tendsto (used by frequency_tendsto_rat),
  frequency_tendsto_rat (step 1), frequency_mono (the last line of steps 3 and 4).
  Write F s for μ.real {ω | X 0 ω ≤ s} and Fₙ(s) for the frequency.
  1. From the good event of frequency_tendsto_rat, introduce ω hω t ht:      R17
  2. The limit through the order; split into the two halves:                R27, constructor, intro a ha
  3. Lower half, ha : a < F t:
       continuity → a δ-ball around t on which a < F s:                      R29 → R30 → R31
       a rational q in (t - δ, t):                                           R32 (side goal by R33)
       hq : a < F ↑q is h applied to a proof of dist ↑q t < δ:              R34, R35, constructor, R33
       eventually a < Fₙ(q) (from hω q), then filter_upwards, and
       frequency_mono lifts it to Fₙ(t):                                     R28, R17, R36
  4. Upper half, ha : a > F t: the mirror image, with gt_mem_nhds and
     q in (t, t + δ):                                                        R29 → R30 → R31, R32, R34, R35, R28, R17, R36
-/
-- BEGIN SPEC
theorem empirical_cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, ContinuousAt (fun s : ℝ => μ.real {ω | X 0 ω ≤ s}) t →
      Tendsto (fun n : ℕ => ((Finset.range n).filter (fun i => X i ω ≤ t)).card / (n : ℝ))
        atTop (𝓝 (μ.real {ω | X 0 ω ≤ t})) :=
-- END SPEC
  by
  filter_upwards [frequency_tendsto_rat μ X hmeas hindep hident] with ω hω t ht
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (lt_mem_nhds ha))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - δ < t by linarith)
    have hq : a < μ.real {ω | X 0 ω ≤ q} :=
      h (by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
    filter_upwards [(tendsto_order.1 (hω q)).1 a hq] with n hn
    exact hn.trans_le (frequency_mono X ω n hq2.le)
  · intro a ha
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (gt_mem_nhds ha))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + δ by linarith)
    have hq : μ.real {ω | X 0 ω ≤ q} < a :=
      h (by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
    filter_upwards [(tendsto_order.1 (hω q)).2 a hq] with n hn
    exact (frequency_mono X ω n hq1.le).trans_lt hn

end H058

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three milestones, then a squeeze. (i) One event `A`: the strong law for the indicators `Yᵢ = 1_A ∘ Xᵢ`
    (bounded, so integrable; independence and law pass through the measurable `1_A`). (ii) `ae_all_iff` turns
    "for each rational `q`, a.s." into "a.s., for all rational `q`" (take `A = Set.Iic q`). (iii) `Fₙ` is
    monotone in `t`, so at a continuity point `t` squeeze `Fₙ(t)` between `Fₙ(q)` and `Fₙ(q')`, `q < t < q'`.
H2. `frequency_tendsto`: `set f : α → ℝ := A.indicator (fun _ => 1)`, `hf := measurable_const.indicator hA`;
    `Integrable.of_bound _ 1`, independence `(hindep hij).comp hf hf`, law `(hident i).comp hf`; the mean via
    `Y 0 = (X 0 ⁻¹' A).indicator (fun _ => 1)` (`rfl`) and `integral_indicator_const`; finish with
    `filter_upwards [strong_law_ae Y hint hind hid]` and `convert hω using 2 with n`. `frequency_mono`: `gcongr`.
    Main: `rw [tendsto_order]` and prove the two halves.
H3. Main: `filter_upwards [frequency_tendsto_rat …] with ω hω t ht`, `rw [tendsto_order]`. Lower half, given `a < F t`:
    `Metric.eventually_nhds_iff.1 (ht.eventually (lt_mem_nhds ha))` gives `δ`; pick `q : ℚ` in `(t - δ, t)` with
    `exists_rat_btwn`; then `(tendsto_order.1 (hω q)).1 a _` is eventually `a < Fₙ(q)`, and
    `hn.trans_le (frequency_mono X ω n hq2.le)` lifts it to `Fₙ(t)`. Upper half: mirror with `gt_mem_nhds`.
-/

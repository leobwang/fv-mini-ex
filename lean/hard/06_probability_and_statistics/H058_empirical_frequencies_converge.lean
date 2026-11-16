/- H058 | Empirical frequencies converge | 1-1.5 h | strong law of large numbers, empirical CDF, indicators, IdentDistrib, ae_all_iff, a.e. filters, filter_upwards, order topology, mathlib
GOAL
  For i.i.d. real samples `X i` (pairwise independent, same law as `X 0`), almost surely the empirical CDF
  `Fₙ(t) = #{i < n | X i ≤ t} / n` tends to the CDF `F(t) = P(X 0 ≤ t)` at every `t` where `F` is continuous, all `t`
  at once. Strong law for one event; `ae_all_iff` over rational `t`; then squeeze `Fₙ(q) ≤ Fₙ(t) ≤ Fₙ(q')`, `q < t < q'`.

REFERENCE
  `X ⟂ᵢ[μ] Y`: independent;  `IdentDistrib X Y μ μ`: same law;  `∀ᵐ ω ∂μ, P ω`: `P` holds a.s.;  `#s` is `s.card`.
  #check strong_law_ae        -- (X) → Integrable (X 0) μ → Pairwise (X i ⟂ᵢ[μ] X j) → (∀ i, IdentDistrib (X i) (X 0) μ μ) →
                              --   ∀ᵐ ω ∂μ, Tendsto (fun n => (↑n)⁻¹ • ∑ i ∈ range n, X i ω) atTop (𝓝 (∫ x, X 0 x ∂μ))
  #check IndepFun.comp        -- X ⟂ᵢ[μ] Y → Measurable φ → Measurable ψ → (φ ∘ X) ⟂ᵢ[μ] (ψ ∘ Y);  same shape: `IdentDistrib.comp`
  #check Integrable.of_bound  -- AEStronglyMeasurable f μ → ∀ C, (∀ᵐ x ∂μ, ‖f x‖ ≤ C) → Integrable f μ;  `Measurable.indicator`
  #check integral_indicator_const  -- (e) → MeasurableSet s → ∫ x, s.indicator (fun _ => e) x ∂μ = μ.real s • e
  #check Finset.sum_boole     -- (∑ x ∈ s, if p x then 1 else 0) = ↑(#{x ∈ s | p x})
  #check ae_all_iff           -- [Countable ι] → ((∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i)   (`ℚ` is `Countable`)
  #check tendsto_order        -- Tendsto f l (𝓝 a) ↔ (∀ a' < a, ∀ᶠ b in l, a' < f b) ∧ ∀ a' > a, ∀ᶠ b in l, f b < a'
  #check exists_rat_btwn      -- x < y → ∃ q : ℚ, x < ↑q ∧ ↑q < y
  #check Metric.eventually_nhds_iff  -- (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ y, dist y x < ε → p y;  `ht.eventually (lt_mem_nhds h)`
  -- `filter_upwards [h] with ω hω`: from `h : ∀ᵐ ω ∂μ, P ω` (or `∀ᶠ`), prove `∀ᵐ ω ∂μ, Q ω` by proving `Q ω` from `hω : P ω`.
NOTE: `(Finset.range n).filter (fun i => X i ω ≤ t)` prints as `{i ∈ Finset.range n | X i ω ≤ t}`; `ContinuousAt f t` unfolds to `Tendsto f (𝓝 t) (𝓝 (f t))`.
-/
import Mathlib

namespace H058

open MeasureTheory ProbabilityTheory Filter Topology

-- MILESTONE (optional: change or delete)
theorem frequency_tendsto {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → α) (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (A : Set α) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((Finset.range n).filter (fun i => X i ω ∈ A)).card / (n : ℝ))
      atTop (𝓝 (μ.real (X 0 ⁻¹' A))) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem frequency_tendsto_rat {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ,
      Tendsto (fun n : ℕ => ((Finset.range n).filter (fun i => X i ω ≤ q)).card / (n : ℝ))
        atTop (𝓝 (μ.real {ω | X 0 ω ≤ q})) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem frequency_mono {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) {s t : ℝ} (hst : s ≤ t) :
    ((Finset.range n).filter (fun i => X i ω ≤ s)).card / (n : ℝ)
      ≤ ((Finset.range n).filter (fun i => X i ω ≤ t)).card / (n : ℝ) := by
  sorry

-- BEGIN SPEC
theorem empirical_cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, ContinuousAt (fun s : ℝ => μ.real {ω | X 0 ω ≤ s}) t →
      Tendsto (fun n : ℕ => ((Finset.range n).filter (fun i => X i ω ≤ t)).card / (n : ℝ))
        atTop (𝓝 (μ.real {ω | X 0 ω ≤ t})) :=
-- END SPEC
  sorry

end H058

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three steps. (i) One event `A`: apply `strong_law_ae` to `Y i = 1_A ∘ X i` (bounded, pairwise independent, same
    law). (ii) `ae_all_iff` turns "for each rational `q`, a.s." into "a.s., for all rational `q`" (take `A = Iic q`).
    (iii) `Fₙ` is monotone in `t`, so at a continuity point `t` squeeze `Fₙ(t)` between `Fₙ(q)` and `Fₙ(q')`.
H2. `frequency_tendsto`: `f := A.indicator (fun _ => (1 : ℝ))`, `hf : Measurable f := measurable_const.indicator hA`;
    independence `(hindep hij).comp hf hf`, law `(hident i).comp hf`, `Integrable.of_bound _ 1`; the mean: `f ∘ X 0 =
    (X 0 ⁻¹' A).indicator (fun _ => 1)` is `rfl`. `frequency_mono`: `gcongr`. Main: prove the two halves of `tendsto_order`.
H3. Main: `filter_upwards [frequency_tendsto_rat …] with ω hω t ht`, `rw [tendsto_order]`. Lower half, given `a < F t`:
    `Metric.eventually_nhds_iff.1 (ht.eventually (lt_mem_nhds ha))` gives `δ`; pick `q : ℚ` in `(t - δ, t)`; then
    `(tendsto_order.1 (hω q)).1 a _` is eventually `a < Fₙ(q)`, and `frequency_mono` lifts it to `Fₙ(t)`. Upper half: mirror.
-/

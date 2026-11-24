/- H051 | Borel–Cantelli lemma | 1-1.5 h | limsup of sets, tsum tails, ENNReal, filters, almost everywhere, mathlib
GOAL
  First Borel–Cantelli lemma: if `∑ P(Aₙ) < ∞` then `P(Aₙ infinitely often) = 0`, where "infinitely often"
  is the set `limsup A atTop = ⋂ n, ⋃ k ≥ n, A k`. Then restate it: almost surely `ω ∉ Aₙ` for all large `n`.
  Finally the countable-index form: for events `A i` indexed by any countable type `ι` (no order, so no
  "large `i`"), `∑ P(Aᵢ) < ∞` implies that almost surely only finitely many `A i` contain `ω`.

REFERENCE
  `∑' i, f i`: infinite sum (`tsum`); in `ℝ≥0∞` it always exists, `≠ ∞` means finite.  `∀ᶠ n in atTop, P n`: for all large `n`.
  `∀ᵐ ω ∂μ, P ω`: `P` holds `μ`-almost everywhere.  `∃ᶠ n in atTop, P n`: for infinitely many `n`.  `𝓝 a`: neighbourhood filter.
  `{x // x ∉ F}`: subtype of `x` outside the finset `F` (`⟨x, hx⟩`, coerced back by `↑`).  `S.Finite`, `S.Infinite = ¬ S.Finite`.
  #check limsup_eq_iInf_iSup_of_nat'  -- limsup u atTop = ⨅ n, ⨆ i, u (i + n)     (on sets `⨅` is `⋂`, `⨆` is `⋃`)
  #check limsup_eq_iInf_iSup_of_nat   -- limsup u atTop = ⨅ n, ⨆ i, ⨆ (_ : i ≥ n), u i
  #check iInf_le                      -- (f i) : iInf f ≤ f i     (`⨆ i, s i` on sets is defeq to `⋃ i, s i`)
  #check measure_iUnion_le            -- (s) : μ (⋃ i, s i) ≤ ∑' i, μ (s i)     (countable subadditivity)
  #check ENNReal.tendsto_sum_nat_add  -- (f) : ∑' i, f i ≠ ∞ → Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)
  #check ge_of_tendsto'               -- Tendsto f x (𝓝 a) → (∀ c, b ≤ f c) → b ≤ a
  #check ae_iff                       -- (∀ᵐ a ∂μ, p a) ↔ μ {a | ¬p a} = 0
  #check Filter.not_eventually        -- (¬∀ᶠ x in f, p x) ↔ ∃ᶠ x in f, ¬p x        (a `simp` lemma)
  #check ENNReal.tendsto_tsum_compl_atTop_zero  -- ∑' x, f x ≠ ∞ → Tendsto (fun F : Finset α => ∑' b : {x // x ∉ F}, f b) atTop (𝓝 0)
  #check Set.Infinite.sdiff           -- S.Infinite → T.Finite → (S \ T).Infinite   (with `Finset.finite_toSet F : (↑F : Set α).Finite`)
  #check Set.Infinite.nonempty        -- S.Infinite → S.Nonempty
BANNED: measure_limsup_atTop_eq_zero, measure_limsup_cofinite_eq_zero, ae_finite_setOf_mem, measure_setOf_frequently_eq_zero, ae_eventually_notMem, measure_liminf_atTop_eq_zero, measure_liminf_cofinite_eq_zero, exact?, apply?, rw?, hint, observe, try?
-/
import Mathlib

namespace H051

open MeasureTheory Filter Topology
open scoped ENNReal

-- MILESTONE (optional: change or delete)
theorem limsup_subset {Ω : Type*} (s : ℕ → Set Ω) (n : ℕ) : limsup s atTop ⊆ ⋃ k, s (k + n) := by
  rw [limsup_eq_iInf_iSup_of_nat']
  exact iInf_le _ n

-- MILESTONE (optional: change or delete)
theorem measure_limsup_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω) (n : ℕ) :
    μ (limsup s atTop) ≤ ∑' k, μ (s (k + n)) := by
  calc μ (limsup s atTop) ≤ μ (⋃ k, s (k + n)) := measure_mono (limsup_subset s n)
    _ ≤ ∑' k, μ (s (k + n)) := measure_iUnion_le _

-- MILESTONE (optional: change or delete)
theorem setOf_not_eventually {Ω : Type*} (s : ℕ → Set Ω) :
    {ω | ¬ ∀ᶠ n in atTop, ω ∉ s n} = limsup s atTop := by
  ext ω
  simp [limsup_eq_iInf_iSup_of_nat]

-- MILESTONE (optional: change or delete)
theorem setOf_infinite_subset {Ω ι : Type*} (s : ι → Set Ω) (F : Finset ι) :
    {ω | ¬ {i | ω ∈ s i}.Finite} ⊆ ⋃ i : {x // x ∉ F}, s i := by
  intro ω hω
  obtain ⟨i, hi, hiF⟩ := (Set.Infinite.sdiff hω F.finite_toSet).nonempty
  exact Set.mem_iUnion.mpr ⟨⟨i, hiF⟩, hi⟩

-- BEGIN SPEC
theorem borel_cantelli {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω)
    (hs : ∑' i, μ (s i) ≠ ∞) : μ (limsup s atTop) = 0 :=
-- END SPEC
  le_antisymm (ge_of_tendsto' (ENNReal.tendsto_sum_nat_add _ hs) (measure_limsup_le μ s)) bot_le

-- BEGIN SPEC
theorem ae_finitely_many {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω)
    (hs : ∑' i, μ (s i) ≠ ∞) : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n :=
-- END SPEC
  by
    rw [ae_iff, setOf_not_eventually]
    exact borel_cantelli μ s hs

-- BEGIN SPEC
theorem ae_finite {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι] (s : ι → Set Ω)
    (hs : ∑' i, μ (s i) ≠ ∞) : ∀ᵐ ω ∂μ, {i | ω ∈ s i}.Finite :=
-- END SPEC
  by
    rw [ae_iff]
    -- WHY: no `atTop` on `ι`; the tails are indexed by finsets `F`, sums over `{x // x ∉ F}`.
    refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun F => ?_) bot_le
    exact (measure_mono (setOf_infinite_subset s F)).trans (measure_iUnion_le _)

end H051

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. For every `n`, `limsup s ⊆ ⋃ k, s (k + n)`, so `μ (limsup s) ≤ ∑' k, μ (s (k + n))`. The right side is a tail of a convergent series, so it tends to `0`; a constant below every term of a sequence tending to `0` is `≤ 0`.
H2. `limsup_subset`: after `rw [limsup_eq_iInf_iSup_of_nat']` the goal is "an infimum is below its `n`-th term". Main: `le_antisymm _ bot_le`, where the first argument is `ge_of_tendsto'` fed the tail limit and `measure_limsup_le μ s`. Second theorem: turn `∀ᵐ` into a null set with `ae_iff`, and identify that set with `limsup s atTop`. Third: the same squeeze, but the "tails" are `∑' b : {x // x ∉ F}, μ (s b)` over finsets `F`; an `ω` in infinitely many `s i` lies in some `s i` with `i ∉ F`.
H3. `setOf_not_eventually`: `ext ω; simp [limsup_eq_iInf_iSup_of_nat]` (both sides become `∀ n, ∃ k ≥ n, ω ∈ s k`). Main: `ge_of_tendsto' (ENNReal.tendsto_sum_nat_add _ hs) (measure_limsup_le μ s)`. Third: `rw [ae_iff]`, then `le_antisymm (ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun F => ?_) bot_le` and close with `measure_mono (setOf_infinite_subset s F)` and `measure_iUnion_le`.
-/

/- H051 | Borel–Cantelli lemma | 1-1.5 h | limsup of sets, tsum tails, ENNReal, filters, almost everywhere, mathlib
GOAL
  First Borel–Cantelli lemma: if `∑ P(Aₙ) < ∞` then `P(Aₙ infinitely often) = 0`, where "infinitely often"
  is the set `limsup A atTop = ⋂ n, ⋃ k ≥ n, A k`. Then restate it: almost surely `ω ∉ Aₙ` for all large `n`.
  Finally the countable-index form: for events `A i` indexed by any countable type `ι` (no order, so no
  "large `i`"), `∑ P(Aᵢ) < ∞` implies that almost surely only finitely many `A i` contain `ω`.

BANNED: measure_limsup_atTop_eq_zero, measure_limsup_cofinite_eq_zero, ae_finite_setOf_mem, measure_setOf_frequently_eq_zero, ae_eventually_notMem, measure_liminf_atTop_eq_zero, measure_liminf_cofinite_eq_zero, exact?, apply?, rw?, hint, observe, try?

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H051

open MeasureTheory Filter Topology
open scoped ENNReal

/- SKELETON · limsup_subset   (milestone; measure_limsup_le uses it)
  1. Rewrite the limsup in its shifted form ⨅ n, ⨆ i, s (i + n):                     R1
  2. The goal is "an intersection ⊆ its n-th member"; close it with the index n:     R2
-/
-- MILESTONE (optional: change or delete)
theorem limsup_subset {Ω : Type*} (s : ℕ → Set Ω) (n : ℕ) : limsup s atTop ⊆ ⋃ k, s (k + n) := by
  sorry

/- SKELETON · measure_limsup_le   (milestone; borel_cantelli uses it for every n)
  1. A two-step calc  μ (limsup s atTop) ≤ μ (⋃ k, s (k + n)) ≤ ∑' k, μ (s (k + n)):  R3
  2. First step: monotonicity with the milestone limsup_subset s n:                  R4
  3. Second step: countable subadditivity:                                           R5
-/
-- MILESTONE (optional: change or delete)
theorem measure_limsup_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω) (n : ℕ) :
    μ (limsup s atTop) ≤ ∑' k, μ (s (k + n)) := by
  sorry

/- SKELETON · setOf_not_eventually   (milestone; ae_finitely_many rewrites with it)
  1. Equality of sets → membership for one ω:                                        R6
  2. One simp call with the unshifted limsup formula; both sides become
     ∀ n, ∃ k, n ≤ k ∧ ω ∈ s k and the goal closes:                                 R7, R8, R9
-/
-- MILESTONE (optional: change or delete)
theorem setOf_not_eventually {Ω : Type*} (s : ℕ → Set Ω) :
    {ω | ¬ ∀ᶠ n in atTop, ω ∉ s n} = limsup s atTop := by
  sorry

/- SKELETON · setOf_infinite_subset   (milestone; ae_finite uses it for every finset F)
  1. Open the ⊆; hω says {i | ω ∈ s i} is infinite:                                  R10
  2. Infinite minus the finite ↑F is infinite, hence nonempty; take i, hi, hiF apart
     in one obtain (call Set.Infinite.sdiff by name, cheatsheet Traps):              R11, R12 → R13 → R14
  3. ω is in the union at the subtype index ⟨i, hiF⟩:                                R16 with R15
-/
-- MILESTONE (optional: change or delete)
theorem setOf_infinite_subset {Ω ι : Type*} (s : ι → Set Ω) (F : Finset ι) :
    {ω | ¬ {i | ω ∈ s i}.Finite} ⊆ ⋃ i : {x // x ∉ F}, s i := by
  sorry

/- SKELETON · borel_cantelli
  0. Prove the milestones limsup_subset and measure_limsup_le first.
  1. μ (limsup s atTop) = 0 from ≤ 0 and ≥ 0:                                        R17
  2. ≤ 0: the constant μ (limsup s atTop) is below every tail ∑' k, μ (s (k + n))
     (measure_limsup_le μ s), and the tails tend to 0:                               R19 fed R20
  3. ≥ 0:                                                                            R18
-/
-- BEGIN SPEC
theorem borel_cantelli {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω)
    (hs : ∑' i, μ (s i) ≠ ∞) : μ (limsup s atTop) = 0 :=
-- END SPEC
  sorry

/- SKELETON · ae_finitely_many
  0. Uses the milestone setOf_not_eventually and borel_cantelli.
  1. ∀ᵐ → the bad set has measure 0:                                                 R21
  2. The bad set is limsup s atTop:                                                  rw [setOf_not_eventually]
  3. That is borel_cantelli μ s hs.
-/
-- BEGIN SPEC
theorem ae_finitely_many {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω)
    (hs : ∑' i, μ (s i) ≠ ∞) : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n :=
-- END SPEC
  sorry

/- SKELETON · ae_finite
  0. Prove the milestone setOf_infinite_subset first.
  1. ∀ᵐ → the bad set μ {a | ¬{i | a ∈ s i}.Finite} = 0:                             R21
  2. The same squeeze as borel_cantelli, along atTop on Finset ι, with a hole for the
     bound under fun F => ?_ :                                                       R17, R19 fed R22, R24, R18
  3. The bound for one F: monotonicity with setOf_infinite_subset s F, then
     subadditivity over the subtype {x // x ∉ F}, chained:                          R4, R5, R23
-/
-- BEGIN SPEC
theorem ae_finite {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι] (s : ι → Set Ω)
    (hs : ∑' i, μ (s i) ≠ ∞) : ∀ᵐ ω ∂μ, {i | ω ∈ s i}.Finite :=
-- END SPEC
  sorry

end H051

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. For every `n`, `limsup s atTop ⊆ ⋃ k, s (k + n)`, so `μ (limsup s atTop) ≤ ∑' k, μ (s (k + n))`: a
    constant below every tail of a convergent series, hence `≤ 0`. The a.e. form is the same statement once
    `∀ᵐ` is a null set (`ae_iff`). For a countable `ι`, replace "the indices `k ≥ n`" by "the indices outside
    a finset `F`".
H2. Milestones in order: `limsup_subset` (R1, R2), `measure_limsup_le` (a `calc` with `measure_mono` and
    `measure_iUnion_le`), `setOf_not_eventually` (`ext ω` and one `simp`), `setOf_infinite_subset` (infinite
    minus finite is nonempty, R10–R16). Main theorems: `le_antisymm _ bot_le` with `ge_of_tendsto'` fed the
    tail limit (`ENNReal.tendsto_sum_nat_add`, resp. `ENNReal.tendsto_tsum_compl_atTop_zero`) and the bound.
H3. `setOf_not_eventually`: `ext ω; simp [limsup_eq_iInf_iSup_of_nat]`. `borel_cantelli`:
    `le_antisymm (ge_of_tendsto' (ENNReal.tendsto_sum_nat_add _ hs) (measure_limsup_le μ s)) bot_le`.
    `ae_finite`: after `rw [ae_iff]`, `refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs)
    fun F => ?_) bot_le`, then `(measure_mono (setOf_infinite_subset s F)).trans (measure_iUnion_le _)`.
-/

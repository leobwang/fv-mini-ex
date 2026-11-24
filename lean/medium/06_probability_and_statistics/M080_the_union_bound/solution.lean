/- M080 | The union bound | 10 min | Finset.induction_on, measure_union_le, Finset sums, ENNReal, mathlib
GOAL
  Boole's inequality: the probability of a finite union is at most the sum of the probabilities.
  Then the corollary used everywhere: if each `μ (A i) ≤ ε`, the union has measure `≤ |s| · ε`.

BANNED: measure_biUnion_finset_le, measure_biUnion_le, measure_iUnion_fintype_le, measure_iUnion_le, exact?, apply?, rw?, hint, try?
GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M080

/- SKELETON · union_bound
  1. The statement has no `DecidableEq ι`, which `insert` needs; get it first:        R1
  2. Induct on `s`, naming the insert case's pieces `a s ha ih`:                       R2
  3. Case `empty`: both sides are `0`; one `simp` applies R3, R4, R5 and closes it
  4. Case `insert`: split `A a` off the union and off the sum:                          R6, R7 (with ha)
       goal becomes  μ (A a ∪ ⋃ x ∈ s, A x) ≤ μ (A a) + ∑ x ∈ s, μ (A x)
  5. Two-set subadditivity first, then compare the two sums termwise:
       `μ (A a)` against itself, the rest against `ih`:                                 R8 → R9, then R10 with R11 and ih
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem union_bound {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι)
    (A : ι → Set Ω) :
    μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i) :=
-- END SPEC
  by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact (measure_union_le _ _).trans (add_le_add le_rfl ih)

/- SKELETON · union_bound_uniform
  Milestone: Part 1 (`union_bound`). No second induction.
  1. A chain of three steps:                                                            R12
       μ (⋃ i ∈ s, A i)  ≤ ∑ i ∈ s, μ (A i)     Part 1, applied to `μ s A`
                         ≤ ∑ i ∈ s, ε            each term bounded by `h`:              R13
                         = ↑s.card * ε           constant sum → `•` → `*`:              R14 → R15
-/
-- BEGIN SPEC
theorem union_bound_uniform {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι)
    (A : ι → Set Ω) (ε : ℝ≥0∞) (h : ∀ i ∈ s, μ (A i) ≤ ε) :
    μ (⋃ i ∈ s, A i) ≤ s.card * ε :=
-- END SPEC
  calc μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i) := union_bound μ s A
    _ ≤ ∑ i ∈ s, ε := Finset.sum_le_sum h
    _ = s.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]

end M080

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induct on the finite set `s` (R1, R2). The empty union has measure `0` and the empty sum is `0`.
    For the corollary do not induct again: use Part 1 and bound each term by `ε`.
H2. In the `insert a s` step split off `A a` on both sides (R6, R7), then chain subadditivity for
    two sets (R8) through `.trans` (R9) with `add_le_add` (R10) of `le_rfl` and `ih`. The corollary is a
    `calc` (R12) through `∑ i ∈ s, ε` (R13), whose constant sum becomes a product (R14, R15).
H3. `rw [Finset.set_biUnion_insert, Finset.sum_insert ha]` leaves
    `μ (A a ∪ ⋃ x ∈ s, A x) ≤ μ (A a) + ∑ x ∈ s, μ (A x)`; `(measure_union_le _ _).trans` reduces it to
    `μ (A a) + μ (⋃ x ∈ s, A x) ≤ μ (A a) + ∑ x ∈ s, μ (A x)`. Last `calc` step:
    `_ = s.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]`.
-/

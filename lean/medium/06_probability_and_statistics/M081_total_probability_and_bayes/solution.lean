/- M081 | Total probability and Bayes | 15 min | cond, partitions, measure_iUnion, simp_rw, ENNReal, mathlib
GOAL
  Law of total probability over a finite measurable partition `B : ι → Set Ω` of `Ω`:
  `μ A = ∑ i, μ[A | B i] * μ (B i)`. Then Bayes' formula for the posterior `μ[B j | A]`.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M081

/- SKELETON · total_probability
  1. Turn every term of the sum into the measure of an intersection. The terms sit under the
     binder `∑ i`, so `rw` fails; use `simp_rw` with R1:                    R1 via R2
       goal becomes  μ A = ∑ x, μ (B x ∩ A)
  2. Prove the cover fact first, with `have` (TACTIC_STATES, "Adding facts"):
       hA' : A = ⋃ i, B i ∩ A        proof: R3 (right to left), rw [hcover], R4
  3. Replace `A` by that union on the LEFT side only:                        R5
  4. Countable additivity, giving both side proofs as arguments:             R6
       disjointness, as `fun i j hij => …` from `hdisj hij`:                 R7 → R8 → R9, R9
       measurability, as `fun i => …` from `hmeas i` and `hA`:              R10
  5. The infinite sum over the finite `ι` → a finite sum (`rw` then closes the goal):   R11
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem total_probability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (hcover : ⋃ i, B i = Set.univ)
    (A : Set Ω) (hA : MeasurableSet A) :
    μ A = ∑ i, μ[A | B i] * μ (B i) :=
-- END SPEC
  by
    simp_rw [cond_mul_eq_inter (hmeas _)]
    have hA' : A = ⋃ i, B i ∩ A := by rw [← Set.iUnion_inter, hcover, Set.univ_inter]
    conv_lhs => rw [hA']
    rw [measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun i => (hmeas i).inter hA), tsum_fintype]

/- SKELETON · bayes
  1. Milestone: Part 1. The denominator is its right side; turn it back into `μ A`:
       rw [← total_probability …]   (give it all of its hypotheses, in order)
  2. Turn the posterior around, `μ[B j | A]` → `(μ A)⁻¹ * μ[A | B j] * μ (B j)`:   R12 (proofs: hA, hmeas j)
  3. Division → multiplication by an inverse:                                R13
  4. Both sides are now the same product, reordered:                         R14
-/
-- BEGIN SPEC
theorem bayes {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (hcover : ⋃ i, B i = Set.univ)
    (A : Set Ω) (hA : MeasurableSet A) (j : ι) :
    μ[B j | A] = μ[A | B j] * μ (B j) / ∑ i, μ[A | B i] * μ (B i) :=
-- END SPEC
  by
    rw [← total_probability μ B hmeas hdisj hcover A hA, cond_eq_inv_mul_cond_mul hA (hmeas j),
      div_eq_mul_inv]
    ring

end M081

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each term `μ[A | B i] * μ (B i)` is `μ (B i ∩ A)` (R1), and the sets `B i ∩ A` are disjoint
    pieces whose union is `A`. In Bayes, the denominator is exactly the right side of Part 1.
H2. Part 1: `simp_rw` the terms into `μ (B i ∩ A)` (R2); prove `A = ⋃ i, B i ∩ A` from `hcover`;
    rewrite only the left `A` (R5); apply countable additivity (R6) and turn `∑'` into `∑` (R11).
    Bayes: rewrite the denominator back to `μ A`, turn the conditional around (R12), replace `/`
    by `* ⁻¹` (R13), and reorder with `ring` (R14).
H3. `have hA' : A = ⋃ i, B i ∩ A := by rw [← Set.iUnion_inter, hcover, Set.univ_inter]`, then
    `conv_lhs => rw [hA']`. Disjointness argument of R6:
    `fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left`.
    Bayes: after `rw [← total_probability μ B hmeas hdisj hcover A hA]`, use `cond_eq_inv_mul_cond_mul hA (hmeas j)`.
-/

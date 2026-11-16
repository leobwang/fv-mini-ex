/- M080 | The union bound | 10 min | Finset.induction_on, measure_union_le, Finset sums, ENNReal, mathlib
GOAL
  Boole's inequality: the probability of a finite union is at most the sum of the probabilities.
  Then the corollary used everywhere: if each `μ (A i) ≤ ε`, the union has measure `≤ |s| · ε`.

REFERENCE
  -- `classical` then `induction s using Finset.induction_on with | empty => _ | insert a s ha ih => _`
  #check Finset.set_biUnion_insert  -- ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x
  #check Finset.sum_insert          -- a ∉ s → ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x
  #check measure_union_le           -- (s t) : μ (s ∪ t) ≤ μ s + μ t
  #check add_le_add                 -- a ≤ b → c ≤ d → a + c ≤ b + d
  #check Finset.sum_le_sum          -- (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
  #check Finset.sum_const           -- ∑ _x ∈ s, b = s.card • b     (then `nsmul_eq_mul`, or `simp`)
  `⋃ i ∈ s, A i` is the union over `s : Finset ι`; `ℝ≥0∞` is `ENNReal`, `s.card` is cast into it.
BANNED: measure_biUnion_finset_le, measure_biUnion_le, measure_iUnion_fintype_le, measure_iUnion_le, exact?, apply?, rw?, hint, try?
-/
import Mathlib

namespace M080

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
H1. Induct on the finite set `s`. The empty union has measure `0`, and the empty sum is `0`.
H2. In the `insert a s` step, split off `A a` on both sides, then use subadditivity for two sets
    and the induction hypothesis for the rest. The corollary is a `calc` through `∑ i ∈ s, ε`.
H3. `rw [Finset.set_biUnion_insert, Finset.sum_insert ha]` leaves
    `μ (A a ∪ ⋃ x ∈ s, A x) ≤ μ (A a) + ∑ x ∈ s, μ (A x)`: chain `measure_union_le` (via `.trans`) with `ih`.
-/

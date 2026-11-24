/- E103 | Conditional expectation | 3 min | condExp, sub-σ-algebra, Measurable[m], mathlib
GOAL
  For a sub-σ-algebra `m` (the information we condition on): averaging `E[X | m]` gives back `E[X]`
  (law of total expectation), and conditioning on `m` leaves an `m`-measurable integrable `X` unchanged.

GUIDE
  Entries R1–R4: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E103

/- SKELETON · integral_condExp_eq
  1. The statement is the library lemma R2 at `hm`; its instance argument
     `[SigmaFinite (μ.trim hm)]` is found automatically:                       R1
  2. Close the goal with that lemma applied to `hm`: the term itself in place
     of `sorry`, or `by exact …`:                                              R2
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem integral_condExp_eq {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    ∫ ω, (μ[X | m]) ω ∂μ = ∫ ω, X ω ∂μ :=
-- END SPEC
  sorry

/- SKELETON · condExp_of_measurable
  1. Replace `sorry` by `by`, then reduce `μ[X | m] = X` to the library
     lemma's two hypotheses (focus each new goal with `·`):                   R4
       → `case hf : StronglyMeasurable[m] X`, `case hfi : Integrable X μ`
  2. `case hf`: convert `hXm : Measurable[m] X` (it prints as `Measurable X`): R3
  3. `case hfi`: the hypothesis `hX`:                                         exact hX
  (Or as one term: R4's lemma with `hm`, R3's term and `hX` as arguments.)
-/
-- BEGIN SPEC
theorem condExp_of_measurable {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXm : Measurable[m] X) (hX : Integrable X μ) :
    μ[X | m] = X :=
-- END SPEC
  sorry

end E103

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each theorem is one Mathlib lemma about `condExp`; the work is passing `hm` and giving each
    hypothesis in the form the lemma wants.
H2. First: `integral_condExp` (R2) holds for every `X`, integrable or not. Second:
    `condExp_of_stronglyMeasurable` (R4) wants `StronglyMeasurable[m] X`, and `hXm.stronglyMeasurable`
    (R3) turns `hXm : Measurable[m] X` into exactly that (the σ-algebra `m` is carried along).
H3. Replace `sorry` by `integral_condExp hm` (or `by exact integral_condExp hm`). Second theorem:
    `condExp_of_stronglyMeasurable hm hXm.stronglyMeasurable hX`.
-/

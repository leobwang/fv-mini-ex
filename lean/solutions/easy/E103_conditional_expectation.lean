/- E103 | Conditional expectation | 3 min | condExp, sub-σ-algebra, Measurable[m], mathlib
GOAL
  For a sub-σ-algebra `m` (the information we condition on): averaging `E[X | m]` gives back `E[X]`
  (law of total expectation), and conditioning on `m` leaves an `m`-measurable integrable `X` unchanged.

REFERENCE
  `μ[X | m]` is `condExp m μ X`, the conditional expectation `E[X | m] : Ω → ℝ` (an m-measurable function).
  (Not E100's `μ[B | A]` = `cond`: here the thing after `|` is a σ-algebra, not a set.)
  `{m mΩ : MeasurableSpace Ω}` with `hm : m ≤ mΩ`: `m` is coarser than the ambient σ-algebra `mΩ`.
  The last-declared σ-algebra (`mΩ`) is the default; `Measurable[m] X` asks for measurability w.r.t. `m`.
  The goal view prints `Measurable[m] X` as `Measurable X`; hover the hypothesis (or
  `set_option pp.explicit true`) to see which σ-algebra it uses.
  #check MeasureTheory.integral_condExp                -- (hm : m ≤ m₀) : ∫ x, μ[f | m] x ∂μ = ∫ x, f x ∂μ
  #check MeasureTheory.condExp_of_stronglyMeasurable   -- (hm) : StronglyMeasurable[m] f → Integrable f μ → μ[f | m] = f
  #check Measurable.stronglyMeasurable                 -- Measurable f → StronglyMeasurable f (for f : Ω → ℝ)
  The instance `SigmaFinite (μ.trim hm)` these lemmas need is found automatically for a probability measure.
NOTE: if `X` is not integrable, Mathlib sets `μ[X | m] = 0`; the identity still holds (both sides are 0).
-/
import Mathlib

namespace E103

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem integral_condExp_eq {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    ∫ ω, (μ[X | m]) ω ∂μ = ∫ ω, X ω ∂μ :=
-- END SPEC
  integral_condExp hm

-- BEGIN SPEC
theorem condExp_of_measurable {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXm : Measurable[m] X) (hX : Integrable X μ) :
    μ[X | m] = X :=
-- END SPEC
  condExp_of_stronglyMeasurable hm hXm.stronglyMeasurable hX

end E103

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems are single library lemmas; the work is passing `hm` and converting hypotheses.
H2. `condExp_of_stronglyMeasurable` wants `StronglyMeasurable[m] X`; `hXm.stronglyMeasurable` turns
    `Measurable[m] X` into exactly that (the σ-algebra `m` is carried along).
H3. Second theorem: `condExp_of_stronglyMeasurable hm hXm.stronglyMeasurable hX`. The first is the
    first `#check`ed lemma applied to `hm`.
-/

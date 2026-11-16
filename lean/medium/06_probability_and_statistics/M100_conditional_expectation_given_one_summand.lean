/- M100 | Conditional expectation given one summand | 15-20 min | condExp, comap σ-algebra, independence, pull-out, filter_upwards, mathlib
GOAL
  For independent `X`, `Y`, condition on `X` (the σ-algebra `σ(X)` of events decided by `X`):
  `E[X + Y | X] = X + E[Y]` and `E[X Y | X] = X · E[Y]`, almost everywhere. Known parts come out,
  independent parts become their mean.

REFERENCE
  `μ[f | m]`: conditional expectation of `f` given the σ-algebra `m`; `MeasurableSpace.comap X inferInstance`
  is `σ(X)`; `f =ᵐ[μ] g`: `f ω = g ω` for μ-almost every `ω`; `μ[Y]` = `∫ ω, Y ω ∂μ`.
  #check @Measurable.comap_le              -- Measurable X → σ(X) ≤ mΩ   (σ(X) is a sub-σ-algebra)
  #check @comap_measurable                 -- X is measurable for σ(X); `.stronglyMeasurable` upgrades it
  #check @condExp_of_stronglyMeasurable    -- f is m-measurable, integrable → μ[f | m] = f
  #check @condExp_indep_eq                 -- f is m₁-measurable, Indep m₁ m₂ μ → μ[f | m₂] =ᵐ fun _ => μ[f]
  #check @condExp_add                      -- μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
  #check @condExp_mul_of_stronglyMeasurable_left  -- f is m-measurable → μ[f * g | m] =ᵐ[μ] f * μ[g | m]
  #check @IndepFun_iff_Indep               -- X ⟂ᵢ[μ] Y (independent) ↔ Indep σ(X) σ(Y) μ; `.symm` swaps
  `h₁.trans h₂` chains `=ᵐ`; `filter_upwards [h] with ω hω` turns an `=ᵐ` goal into a pointwise one.
-/
import Mathlib

namespace M100

open MeasureTheory ProbabilityTheory

-- BEGIN SPEC
theorem condExp_add_given_first {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) (hXY : X ⟂ᵢ[μ] Y) :
    μ[fun ω => X ω + Y ω | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => X ω + μ[Y] :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem condExp_mul_given_first {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hYi : Integrable Y μ) (hXYi : Integrable (fun ω => X ω * Y ω) μ) (hXY : X ⟂ᵢ[μ] Y) :
    μ[fun ω => X ω * Y ω | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => X ω * μ[Y] :=
-- END SPEC
  sorry

end M100

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three facts: `μ[X | σ(X)] = X` (X is known), `μ[Y | σ(X)] =ᵐ fun _ => μ[Y]` (Y is independent of
    σ(X)), and pull-out for the product. Prove the first two as `have`s (maybe as a helper lemma).
H2. For `condExp_indep_eq` take `m₁ = σ(Y)`, `m₂ = σ(X)`: the independence you need is
    `Indep σ(Y) σ(X)`, i.e. `((IndepFun_iff_Indep _ _ _).mp hXY).symm`.
H3. Sum: `refine (condExp_add hXi hYi _).trans ?_; filter_upwards [h2] with ω hω; simp [h1, hω]`.
    Product: `refine (condExp_mul_of_stronglyMeasurable_left hXm hXYi hYi).trans ?_` and the same finish.
-/

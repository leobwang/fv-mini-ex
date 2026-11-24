/- M100 | Conditional expectation given one summand | 15-20 min | condExp, comap σ-algebra, independence, pull-out, filter_upwards, mathlib
GOAL
  For independent `X`, `Y`, condition on `X` (the σ-algebra `σ(X)` of events decided by `X`):
  `E[X + Y | X] = X + E[Y]` and `E[X Y | X] = X · E[Y]`, almost everywhere. Known parts come out,
  independent parts become their mean.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M100

open MeasureTheory ProbabilityTheory

/-- `X` is known given `σ(X)`, and the independent `Y` averages out to its mean. -/
theorem known_and_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : X ⟂ᵢ[μ] Y) :
    StronglyMeasurable[MeasurableSpace.comap X inferInstance] X ∧
      μ[Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun _ => μ[Y] :=
  ⟨(comap_measurable X).stronglyMeasurable,
    -- WHY: `condExp_indep_eq` wants the σ-algebra of the averaged function first, hence `.symm`.
    condExp_indep_eq hY.comap_le hX.comap_le (comap_measurable Y).stronglyMeasurable
      ((IndepFun_iff_Indep _ _ _).mp hXY).symm⟩

/- SKELETON · condExp_add_given_first
  Write σ(X) for `MeasurableSpace.comap X inferInstance`.
  1. Facts first, as `have`s (or one helper lemma shared with the product theorem):
       sub-σ-algebras  hX.comap_le : σ(X) ≤ mΩ,  hY.comap_le : σ(Y) ≤ mΩ          R1
       hXm : StronglyMeasurable[σ(X)] X        (write the type out)              R2 → R3
       h2 : μ[Y | σ(X)] =ᵐ[μ] fun _ => μ[Y]    Y averages out:
              R6 with f := Y, m₁ := σ(Y), m₂ := σ(X); Y's measurability R2 → R3;
              independence in the order Indep σ(Y) σ(X) μ                        R4 → R5
       h1 : μ[X | σ(X)] = X                    X is known                        R7 (with R1, hXm)
  2. Split the conditional expectation of the sum (an =ᵐ, so not `rw`):          R9 through R8
  3. Go pointwise, taking h2 along:                                              R11
  4. Unfold the sum of functions, then substitute h1 and hω:                     R12, rw [h1, hω]
-/
-- BEGIN SPEC
theorem condExp_add_given_first {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) (hXY : X ⟂ᵢ[μ] Y) :
    μ[fun ω => X ω + Y ω | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => X ω + μ[Y] :=
-- END SPEC
  by
    obtain ⟨hXm, h2⟩ := known_and_indep μ X Y hX hY hXY
    have h1 : μ[X | MeasurableSpace.comap X inferInstance] = X :=
      condExp_of_stronglyMeasurable hX.comap_le hXm hXi
    refine (condExp_add hXi hYi _).trans ?_
    filter_upwards [h2] with ω hω
    simp [h1, hω]

/- SKELETON · condExp_mul_given_first
  1. The same facts hXm and h2 as above (a `have` belongs to one proof only):    R1, R2 → R3, R4 → R5, R6
     No h1 here: the known factor X is pulled out, not averaged.
  2. Pull the known factor X out of the conditional expectation:                 R10 through R8
  3. Go pointwise, taking h2 along:                                              R11
  4. Unfold the product of functions, then substitute hω:                        R13, rw [hω]
-/
-- BEGIN SPEC
theorem condExp_mul_given_first {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hYi : Integrable Y μ) (hXYi : Integrable (fun ω => X ω * Y ω) μ) (hXY : X ⟂ᵢ[μ] Y) :
    μ[fun ω => X ω * Y ω | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => X ω * μ[Y] :=
-- END SPEC
  by
    obtain ⟨hXm, h2⟩ := known_and_indep μ X Y hX hY hXY
    refine (condExp_mul_of_stronglyMeasurable_left hXm hXYi hYi).trans ?_
    filter_upwards [h2] with ω hω
    simp [hω]

end M100

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three facts: `μ[X | σ(X)] = X` (X is known), `μ[Y | σ(X)] =ᵐ fun _ => μ[Y]` (Y is independent of
    σ(X)), and pull-out for the product. Prove the first two as `have`s before touching the goal
    (or in a helper lemma both theorems use).
H2. The condExp lemmas give `=ᵐ`, so chain them with `refine (lemma …).trans ?_`, then
    `filter_upwards [h2] with ω hω` and finish at the point `ω`. For `condExp_indep_eq` take
    `m₁ = σ(Y)`, `m₂ = σ(X)`: the independence it needs is `Indep σ(Y) σ(X)`, i.e.
    `((IndepFun_iff_Indep _ _ _).mp hXY).symm`.
H3. Sum: `refine (condExp_add hXi hYi _).trans ?_; filter_upwards [h2] with ω hω; simp [h1, hω]`
    (or `rw [Pi.add_apply, h1, hω]`). Product:
    `refine (condExp_mul_of_stronglyMeasurable_left hXm hXYi hYi).trans ?_` and the same finish
    without `h1`.
-/

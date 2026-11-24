/- Guide for M100 (Conditional expectation given one summand).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other variables `Z`, `W`,
abstract functions `F f g`).
Assumed: Lean basics. Mathlib's measure theory is explained in cheatsheet.md.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace M100Guide

/-! # Part R · Reference entries -/

/-! ## Measurability with respect to `σ(X)` -/

/-! ### R1. `Measurable.comap_le` · context gains `σ(X) ≤ mΩ` (σ(X) is a sub-σ-algebra)
Written as dot notation on the measurability proof: `hX.comap_le`. -/
example {Ω : Type} [mΩ : MeasurableSpace Ω] (X : Ω → ℝ) (hX : Measurable X) (P : Prop)
    (h : MeasurableSpace.comap X inferInstance ≤ mΩ → P) : P := by
  have hle := hX.comap_le
  exact h hle

/-! ### R2. `comap_measurable` · context gains `Measurable[σ(X)] X` (X is σ(X)-measurable)
The infoview hides the σ-algebra: it prints `Measurable X`. -/
example {Ω : Type} (X : Ω → ℝ) (P : Prop)
    (h : Measurable[MeasurableSpace.comap X inferInstance] X → P) : P := by
  have hm : Measurable[MeasurableSpace.comap X inferInstance] X := comap_measurable X
  exact h hm

/-! ### R3. `Measurable.stronglyMeasurable` · context: `Measurable[m] f` → `StronglyMeasurable[m] f`
For `f : Ω → ℝ` the two notions agree; the condExp lemmas ask for the strong one. -/
example {Ω : Type} (m : MeasurableSpace Ω) (f : Ω → ℝ) (hf : Measurable[m] f) (P : Prop)
    (h : StronglyMeasurable[m] f → P) : P := by
  have hs := hf.stronglyMeasurable
  exact h hs

/-! ## Independence as σ-algebras -/

/-! ### R4. `IndepFun_iff_Indep` · context: `X ⟂ᵢ[μ] Y` → `Indep σ(X) σ(Y) μ` (with `.mp`) -/
example {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) (hXY : X ⟂ᵢ[μ] Y)
    (P : Prop)
    (h : Indep (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap Y inferInstance) μ → P) :
    P := by
  have hI := (IndepFun_iff_Indep X Y μ).mp hXY
  exact h hI

/-! ### R5. `Indep.symm` · context: `Indep m₁ m₂ μ` → `Indep m₂ m₁ μ` -/
example {Ω : Type} {m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (hI : Indep m₁ m₂ μ) (P : Prop) (h : Indep m₂ m₁ μ → P) : P := by
  have hI' := hI.symm
  exact h hI'

/-! ## Conditional expectation: what comes out, what averages out -/

/-! ### R6. `condExp_indep_eq` · closes `μ[f | m₂] =ᵐ[μ] fun _ => ∫ f` when `f` is
`m₁`-measurable and `m₁`, `m₂` are independent. Argument order: `m₁ ≤ mΩ`, `m₂ ≤ mΩ`,
`StronglyMeasurable[m₁] f`, `Indep m₁ m₂ μ`: the σ-algebra of `f` comes FIRST in `Indep`. -/
example {Ω : Type} {m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    (hf : StronglyMeasurable[m₁] f) (hI : Indep m₁ m₂ μ) :
    μ[f | m₂] =ᵐ[μ] fun _ => ∫ ω, f ω ∂μ := by
  exact condExp_indep_eq h₁ h₂ hf hI

/-! ### R7. `condExp_of_stronglyMeasurable` · goal: `μ[f | m]` → `f` when `f` is `m`-measurable
Arguments: `m ≤ mΩ`, `StronglyMeasurable[m] f`, `Integrable f μ`. This is an `=`, so `rw` works. -/
example {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hm : m ≤ mΩ) (hf : StronglyMeasurable[m] f)
    (hfi : Integrable f μ) (P : (Ω → ℝ) → Prop) (h : P f) : P μ[f | m] := by
  rw [condExp_of_stronglyMeasurable hm hf hfi]
  exact h

/-! ## Almost-everywhere equalities -/

/-! ### R8. `Filter.EventuallyEq.trans` · goal `f =ᵐ[μ] k` → `g =ᵐ[μ] k`, given `h₁ : f =ᵐ[μ] g`
Write `refine h₁.trans ?_`: the first link is supplied now, the second becomes the goal. -/
example {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (f g k : Ω → ℝ)
    (h₁ : f =ᵐ[μ] g) (h : g =ᵐ[μ] k) : f =ᵐ[μ] k := by
  refine h₁.trans ?_
  exact h

/-! ### R9. `condExp_add` · goal: `μ[f + g | m]` → `μ[f | m] + μ[g | m]`, up to `=ᵐ`
Arguments: `Integrable f μ`, `Integrable g μ`, then `m`. It is an `=ᵐ`, not an `=`: use it as the
first link of R8, not with `rw`. -/
example {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (f g k : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (h : μ[f | m] + μ[g | m] =ᵐ[μ] k) : μ[f + g | m] =ᵐ[μ] k := by
  refine (condExp_add hf hg m).trans ?_
  exact h

/-! ### R10. `condExp_mul_of_stronglyMeasurable_left` · goal: `μ[f * g | m]` → `f * μ[g | m]`, up to
`=ᵐ` ("pull out what is known"). Arguments: `StronglyMeasurable[m] f`, `Integrable (f * g) μ`,
`Integrable g μ`. -/
example {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (f g k : Ω → ℝ) (hf : StronglyMeasurable[m] f) (hfg : Integrable (f * g) μ)
    (hg : Integrable g μ) (h : f * μ[g | m] =ᵐ[μ] k) : μ[f * g | m] =ᵐ[μ] k := by
  refine (condExp_mul_of_stronglyMeasurable_left hf hfg hg).trans ?_
  exact h

/-! ### R11. `filter_upwards [h] with ω hω` · goal `F =ᵐ[μ] G` → `F ω = G ω` for a fresh point `ω`;
context gains `ω` and `hω`, the pointwise form of each listed `=ᵐ` hypothesis `h`. -/
example {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (h : f =ᵐ[μ] g) :
    (fun ω => f ω + 1) =ᵐ[μ] fun ω => g ω + 1 := by
  filter_upwards [h] with ω hω
  rw [hω]

/-! ### R12. `Pi.add_apply` · goal: `(f + g) ω` → `f ω + g ω` (`simp` applies it by itself) -/
example {Ω : Type} (f g : Ω → ℝ) (ω : Ω) (P : ℝ → Prop) (h : P (f ω + g ω)) : P ((f + g) ω) := by
  rw [Pi.add_apply]
  exact h

/-! ### R13. `Pi.mul_apply` · goal: `(f * g) ω` → `f ω * g ω` (`simp` applies it by itself) -/
example {Ω : Type} (f g : Ω → ℝ) (ω : Ω) (P : ℝ → Prop) (h : P (f ω * g ω)) : P ((f * g) ω) := by
  rw [Pi.mul_apply]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An independent variable averages out: R1, R2, R3, R4, R6
Here the independence is already in the order R6 wants (`σ(Z)` first), so R5 is not needed. -/
example {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z W : Ω → ℝ) (hZ : Measurable Z) (hW : Measurable W) (hZW : Z ⟂ᵢ[μ] W) :
    μ[Z | MeasurableSpace.comap W inferInstance] =ᵐ[μ] fun _ => ∫ ω, Z ω ∂μ := by
  have hZm : StronglyMeasurable[MeasurableSpace.comap Z inferInstance] Z :=
    (comap_measurable Z).stronglyMeasurable
  exact condExp_indep_eq hZ.comap_le hW.comap_le hZm ((IndepFun_iff_Indep Z W μ).mp hZW)

/-! ### W2. Chaining `=ᵐ` and finishing pointwise: R8, R11, R12, then `rw` -/
example {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (F f g : Ω → ℝ) (c : ℝ)
    (h₁ : F =ᵐ[μ] f + g) (h₂ : g =ᵐ[μ] fun _ => c) : F =ᵐ[μ] fun ω => f ω + c := by
  refine h₁.trans ?_
  filter_upwards [h₂] with ω hω
  rw [Pi.add_apply, hω]

end M100Guide

/- Guide for E125 (Momentum is dimensionally correct).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (area `A = a · a`, distance `v · t`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Units.WithDim.Speed

open Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim WithDim

namespace E125Guide

/-! # Part R · Reference entries -/

/-! ## Dimensional correctness of a function → one equation per input -/

/-! ### R1. `isDimensionallyCorrect_fun_iff` · goal: `IsDimensionallyCorrect f` → a `∀` over unit systems
`IsDimensionallyCorrect x` means `∀ u1 u2, scaleUnit u1 u2 x = x`. For a function `f` the lemma unfolds
`scaleUnit` on functions: convert the input `u2 → u1`, apply `f`, convert the output `u1 → u2`. -/
example {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (f : M1 → M2)
    (h : ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m) : IsDimensionallyCorrect f := by
  rw [isDimensionallyCorrect_fun_iff]
  exact h

/-! ### R2. `funext x y` · goal: `f = g` (functions of two arguments) → `f x y = g x y`; context gains `x y` -/
example {α β : Type} (f g : α → β → Prop) (h : ∀ x y, f x y = g x y) : f = g := by
  funext x y
  exact h x y

/-! ## Pushing `scaleUnit` onto the arguments -/

/-! ### R3. `scaleUnit_apply_fun` · goal: a rescaled function applied to `m` → rescale `m` back, apply, rescale
The output type `M2` carries units too (`[UnitDependent M2]`), so the output is rescaled as well. -/
example {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (u1 u2 : LTMCTUnitChoices) (f : M1 → M2)
    (m : M1) (P : M2 → Prop) (h : P (scaleUnit u1 u2 (f (scaleUnit u2 u1 m)))) :
    P (scaleUnit u1 u2 f m) := by
  rw [scaleUnit_apply_fun]
  exact h

/-! ### R4. `scaleUnit_apply_fun_left` · goal: the same when the output (here `Prop`) carries no units
Only the input is rescaled: a proposition has no dimension. -/
example {M1 : Type} [UnitDependent M1] (u1 u2 : LTMCTUnitChoices) (f : M1 → Prop) (m : M1)
    (P : Prop → Prop) (h : P (f (scaleUnit u2 u1 m))) : P (scaleUnit u1 u2 f m) := by
  rw [scaleUnit_apply_fun_left]
  exact h

/-! ### R5. Unfold a definition: `simp only [D]` · goal: `D a b` → the body of `D` -/
def D {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (P : Prop → Prop) (h : P (a = b)) : P (D a b) := by
  simp only [D]
  exact h

/-! ## Moving `scaleUnit` outward through `*` and `cast` -/

/-! ### R6. `DMul.hMul_scaleUnit` · goal: product of rescaled quantities → rescaled product
`x * y : WithDim (d1 * d2) ℝ` multiplies the values and the dimensions. -/
example (d1 d2 : Dimension LTMCTDimensionBase) (u1 u2 : LTMCTUnitChoices) (x : WithDim d1 ℝ)
    (y : WithDim d2 ℝ) (P : WithDim (d1 * d2) ℝ → Prop) (h : P (scaleUnit u1 u2 (x * y))) :
    P (scaleUnit u1 u2 x * scaleUnit u1 u2 y) := by
  rw [DMul.hMul_scaleUnit]
  exact h

/-! ### R7. `WithDim.cast_scaleUnit` · goal: `cast` of a rescaled quantity → rescaled `cast`
`x.cast h : WithDim d2 ℝ` is `x : WithDim d ℝ` with the same value, retyped along a proof `h : d = d2`. -/
example (d d2 : Dimension LTMCTDimensionBase) (hd : d = d2) (u1 u2 : LTMCTUnitChoices)
    (x : WithDim d ℝ) (P : WithDim d2 ℝ → Prop) (h : P (scaleUnit u1 u2 (x.cast hd))) :
    P ((scaleUnit u1 u2 x).cast hd) := by
  rw [cast_scaleUnit]
  exact h

/-! ### R8. `scaleUnit_injective` · `scaleUnit u1 u2 a = scaleUnit u1 u2 b ↔ a = b` · goal
`rw` with an `↔` lemma replaces one proposition by the other. -/
example {M : Type} [UnitDependent M] (u1 u2 : LTMCTUnitChoices) (a b : M) (P : Prop → Prop)
    (h : P (a = b)) : P (scaleUnit u1 u2 a = scaleUnit u1 u2 b) := by
  rw [scaleUnit_injective]
  exact h

/-! ### R9. `rw` closes the goal by `rfl` · goal list: a goal that became `X = X` is closed
After every `rw`, Lean tries `rfl`; when both sides are now the same text, no goal is left. -/
example {M : Type} [UnitDependent M] (u1 u2 : LTMCTUnitChoices) (a b : M) :
    (scaleUnit u1 u2 a = scaleUnit u1 u2 b) = (a = b) := by
  rw [scaleUnit_injective]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- The area of a square of side `a`: `A = a · a`. -/
def AreaEq (a : WithDim L𝓭 ℝ) (A : WithDim (L𝓭 * L𝓭) ℝ) : Prop := A = a * a

/-! ### W1. Two arguments and no `cast`: R1, `intro`, R2 (one variable), R4, R5, R6, R8 + R9
With only two arguments, the rescaled function is applied once, so R4 alone is enough. -/
example : IsDimensionallyCorrect AreaEq := by
  rw [isDimensionallyCorrect_fun_iff]
  intro u1 u2 a
  funext A
  simp only [scaleUnit_apply_fun_left, AreaEq]
  rw [DMul.hMul_scaleUnit, scaleUnit_injective]

/-! ### W2. A `cast` around a product: R6, then R7
`v * t : WithDim (L𝓭 * T𝓭⁻¹ * T𝓭) ℝ` and `L𝓭 * T𝓭⁻¹ * T𝓭 = L𝓭`; `cast` finds that proof itself. -/
example (u1 u2 : LTMCTUnitChoices) (v : WithDim (L𝓭 * T𝓭⁻¹) ℝ) (t : WithDim T𝓭 ℝ)
    (x : WithDim L𝓭 ℝ) (h : x = scaleUnit u1 u2 (cast (v * t) : WithDim L𝓭 ℝ)) :
    x = (cast (scaleUnit u1 u2 v * scaleUnit u1 u2 t) : WithDim L𝓭 ℝ) := by
  rw [DMul.hMul_scaleUnit]
  rw [cast_scaleUnit]
  exact h

end E125Guide

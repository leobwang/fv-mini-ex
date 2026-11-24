/- Guide for M188 (Kinetic energy is dimensionally correct).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal or
hypothesis became. `G : Prop` is a goal the entry does not touch.
Part W: worked combinations on an object that is NOT the exercise's (the relation `x = v t`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Units.WithDim.Speed

open Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim WithDim

namespace M188Guide

/-! # Part R · Reference entries -/

/-! ## Dimensional correctness → "rescaled relation ↔ relation"
`simp [funext_iff, D]` applies R1–R8 by itself; each is shown alone here. -/

/-! ### R1. `isDimensionallyCorrect_fun_iff` · goal: `IsDimensionallyCorrect f` → a `∀` over unit systems
`IsDimensionallyCorrect f` means `scaleUnit u1 u2 f = f` for all unit systems `u1 u2`; for a function
`f` this says: convert the input `u2 → u1`, apply `f`, convert the output `u1 → u2`, and you get `f m`. -/
example {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (f : M1 → M2)
    (h : ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m) : IsDimensionallyCorrect f := by
  rw [isDimensionallyCorrect_fun_iff]
  exact h

/-! ### R2. `funext_iff` · goal: `f = g` (functions) → `∀ x, f x = g x` -/
example {α β : Type} (f g : α → β) (h : ∀ x, f x = g x) : f = g := by
  rw [funext_iff]
  exact h

/-! ### R3. `scaleUnit_apply_fun` · goal: rescaled function applied to `m` → rescale `m` back, apply, rescale
The output type `M2` carries units too (`[UnitDependent M2]`), so the output is rescaled as well. -/
example {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (u1 u2 : LTMCTUnitChoices) (f : M1 → M2)
    (m : M1) (P : M2 → Prop) (h : P (scaleUnit u1 u2 (f (scaleUnit u2 u1 m)))) :
    P (scaleUnit u1 u2 f m) := by
  rw [scaleUnit_apply_fun]
  exact h

/-! ### R4. `scaleUnit_apply_fun_left` · goal: same, when the output (here `Prop`) carries no units
Only the input is rescaled: a proposition has no dimension. -/
example {M1 : Type} [UnitDependent M1] (u1 u2 : LTMCTUnitChoices) (f : M1 → Prop) (m : M1)
    (P : Prop → Prop) (h : P (f (scaleUnit u2 u1 m))) : P (scaleUnit u1 u2 f m) := by
  rw [scaleUnit_apply_fun_left]
  exact h

/-! ### R5. `eq_iff_iff` · goal: an equation of propositions `p = q` → `p ↔ q` -/
example (p q : Prop) (h : p ↔ q) : p = q := by
  rw [eq_iff_iff]
  exact h

/-! ### R6. `one_div` · `1 / a = a⁻¹` · goal: `1 / a` → `a⁻¹` (`simp` writes `1/2` as `2⁻¹`) -/
example {α : Type} [DivInvMonoid α] (a : α) (P : α → Prop) (h : P a⁻¹) : P (1 / a) := by
  rw [one_div]
  exact h

/-! ### R7. `val_pow_two_eq_mul` · `x.val ^ 2 = (x * x).val` · goal: a square of a raw number → a product of quantities
`x * x : WithDim (d * d) ℝ` multiplies the values and the dimensions. -/
example {B : Type} {d : Dimension B} (x : WithDim d ℝ) (P : ℝ → Prop) (h : P (x * x).val) :
    P (x.val ^ 2) := by
  rw [val_pow_two_eq_mul]
  exact h

/-! ### R8. `DMul.hMul_scaleUnit` · goal: product of rescaled quantities → rescaled product -/
example (d1 d2 : Dimension LTMCTDimensionBase) (u1 u2 : LTMCTUnitChoices) (x : WithDim d1 ℝ)
    (y : WithDim d2 ℝ) (P : WithDim (d1 * d2) ℝ → Prop) (h : P (scaleUnit u1 u2 (x * y))) :
    P (scaleUnit u1 u2 x * scaleUnit u1 u2 y) := by
  rw [DMul.hMul_scaleUnit]
  exact h

/-! ## Rescaled values → real numbers times scale factors -/

/-! ### R9. `WithDim.scaleUnit_val` · goal: value of a rescaled quantity → factor `•` value -/
example (d : Dimension LTMCTDimensionBase) (u1 u2 : LTMCTUnitChoices) (x : WithDim d ℝ)
    (P : ℝ → Prop) (h : P ((u1.dimScale u2) d • x.val)) : P (scaleUnit u1 u2 x).val := by
  rw [WithDim.scaleUnit_val]
  exact h

/-! ### R10. `WithDim.withDim_hMul_val` · goal: value of a product → product of values -/
example {B : Type} {d1 d2 : Dimension B} (x : WithDim d1 ℝ) (y : WithDim d2 ℝ) (P : ℝ → Prop)
    (h : P (x.val * y.val)) : P (x * y).val := by
  rw [WithDim.withDim_hMul_val]
  exact h

/-! ### R11. `map_mul` · `f (x * y) = f x * f y` for a monoid hom `f : M →* N` · goal
`u1.dimScale u2 : Dimension LTMCTDimensionBase →* NNReal` is such an `f`. -/
example {M N : Type} [MulOneClass M] [MulOneClass N] (f : M →* N) (x y : M) (P : N → Prop)
    (h : P (f x * f y)) : P (f (x * y)) := by
  rw [map_mul]
  exact h

/-! ### R12. `map_inv` · `f a⁻¹ = (f a)⁻¹` for a monoid hom out of a group · goal -/
example {G H : Type} [Group G] [DivisionMonoid H] (f : G →* H) (a : G) (P : H → Prop)
    (h : P (f a)⁻¹) : P (f a⁻¹) := by
  rw [map_inv]
  exact h

/-! ### R13. `NNReal.smul_def` · `c • x = ↑c • x` · goal: `NNReal` scalar → its real cast -/
example (c : NNReal) (x : ℝ) (P : ℝ → Prop) (h : P ((c : ℝ) • x)) : P (c • x) := by
  rw [NNReal.smul_def]
  exact h

/-! ### R14. `smul_eq_mul` · `a • b = a * b` when both live in the same type · goal -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R15. `NNReal.coe_mul` · `↑(r * s) = ↑r * ↑s` · goal: the cast to `ℝ` moves inside `*` -/
example (r s : NNReal) (P : ℝ → Prop) (h : P ((r : ℝ) * s)) : P ((r * s : NNReal) : ℝ) := by
  rw [NNReal.coe_mul]
  exact h

/-! ### R16. `NNReal.coe_inv` · `↑r⁻¹ = (↑r)⁻¹` · goal: the cast to `ℝ` moves inside `⁻¹` -/
example (r : NNReal) (P : ℝ → Prop) (h : P (r : ℝ)⁻¹) : P ((r⁻¹ : NNReal) : ℝ) := by
  rw [NNReal.coe_inv]
  exact h

/-! ## Scale factors are nonzero -/

/-! ### R17. `dimScale_pos` · context gains `0 < (u1.dimScale u2) d` -/
example (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) (G : Prop)
    (k : 0 < (u1.dimScale u2) d → G) : G := by
  have hpos := dimScale_pos u1 u2 d
  exact k hpos

/-! ### R18. `.ne'` (`LT.lt.ne'`) · `a < b → b ≠ a` · context gains `h : s ≠ 0` from `hs : 0 < s` -/
example (s : NNReal) (hs : 0 < s) (G : Prop) (k : s ≠ 0 → G) : G := by
  have h := hs.ne'
  exact k h

/-! ## Proving the `↔` -/

/-! ### R19. `constructor` on `A ↔ B` · goal list: one goal → `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (h1 : A → B) (h2 : B → A) : A ↔ B := by
  constructor
  exact h1
  exact h2

/-! ### R20. `field_simp at h` · context: `h` with nonzero factors and inverses → cleared, normalised `h`
It cancels a factor on both sides when it knows the factor is `≠ 0` (here from `hs`), and multiplies
out inverses such as `2⁻¹`. It reads `s ≠ 0` for `s : NNReal` as `(↑s : ℝ) ≠ 0` by itself. -/
example (s : NNReal) (hs : s ≠ 0) (x y : ℝ) (G : Prop) (h : ↑s * x = 2⁻¹ * (↑s * y))
    (k : x * 2 = y → G) : G := by
  field_simp at h
  exact k h

/-! ### R21. `linear_combination e` · closes `a = b` when `a - b = c · (lhs - rhs of h)` is a ring identity
`linear_combination h / 2` uses the hypothesis `h` scaled by `1/2`. -/
example (x y : ℝ) (h : x * 2 = y) : x = 2⁻¹ * y := by
  linear_combination h / 2

/-! ### R22. `field_simp` · closes a goal that becomes trivial after clearing nonzero denominators -/
example (s t : NNReal) (ht : t ≠ 0) (y : ℝ) :
    ↑s * (↑t)⁻¹ * (2⁻¹ * y) = 2⁻¹ * (↑s * y) * (↑t)⁻¹ := by
  field_simp

/-! # Part W · Worked combinations (not the exercise's object) -/

/-- Distance travelled at constant speed, `x = v t`, on the raw numbers. -/
def Distance (v : WithDim (L𝓭 * T𝓭⁻¹) ℝ) (t : WithDim T𝓭 ℝ) (x : WithDim L𝓭 ℝ) : Prop :=
  x.1 = v.1 * t.1

/-! ### W1. The whole chain on `Distance`: R1–R8 by `simp`, R9–R16 by `simp only`, R17–R20, R22
Here the forward direction needs no `linear_combination`: `field_simp at h` already leaves `h` as the goal. -/
example : IsDimensionallyCorrect Distance := by
  simp [funext_iff, Distance]
  intro u1 u2 v t x
  simp only [WithDim.scaleUnit_val, WithDim.withDim_hMul_val, map_mul, map_inv,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_mul, NNReal.coe_inv]
  have hL := (dimScale_pos u2 u1 L𝓭).ne'
  have hT := (dimScale_pos u2 u1 T𝓭).ne'
  constructor <;> intro h
  · field_simp at h
    exact h
  · rw [h]
    field_simp

end M188Guide

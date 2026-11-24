/- Guide for M189 (E = c·m·v is not dimensionally correct).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the relation `p = m`).
Assumed: Lean basics (E001–E033). Physlib's units library is explained entry by entry.
-/
import Physlib.Units.WithDim.Speed

open Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim WithDim

namespace M189Guide

/-! # Part R · Reference entries -/

/-! ## From "dimensionally correct" to a counterexample goal -/

/-! ### R1. `isDimensionallyCorrect_fun_iff` · goal: `IsDimensionallyCorrect f` → a `∀` over unit systems and inputs
`f` is dimensionally correct when, for all unit systems `u1 u2`, converting the input from `u2` to `u1`
(`scaleUnit u2 u1 m` is "`m` given in `u2`, re-expressed in `u1`"), applying `f`, and converting the
output from `u1` back to `u2` gives `f m` again. -/
example {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (f : M1 → M2)
    (h : ¬ ∀ u1 u2 : LTMCTUnitChoices, ∀ m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m) :
    ¬ IsDimensionallyCorrect f := by
  rw [isDimensionallyCorrect_fun_iff]
  exact h

/-! ### R2. `not_forall` · `(¬ ∀ x, p x) ↔ ∃ x, ¬ p x` · goal: push `¬` through a `∀` -/
example {α : Type} (p : α → Prop) (h : ∃ x, ¬ p x) : ¬ ∀ x, p x := by
  rw [not_forall]
  exact h

/-! ### R3. `funext_iff` · `f = g ↔ ∀ x, f x = g x` · goal: equation of functions → pointwise -/
example {α β : Type} (f g : α → β) (h : ¬ ∀ x, f x = g x) : ¬ f = g := by
  rw [funext_iff]
  exact h

/-! ### R4. `scaleUnit_apply_fun` · goal: rescaled function applied to `m` → rescale `m` back, apply, rescale -/
example {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (u1 u2 : LTMCTUnitChoices)
    (f : M1 → M2) (m : M1) (P : M2 → Prop) (h : P (scaleUnit u1 u2 (f (scaleUnit u2 u1 m)))) :
    P (scaleUnit u1 u2 f m) := by
  rw [scaleUnit_apply_fun]
  exact h

/-! ## Choosing the counterexample -/

/-! ### R5. `use a, b` · goal `∃ x y z, P x y z` → the witnesses are filled in, left to right
`use` then tries `rfl`/`assumption` on what is left; here it cannot, so one `∃` remains. -/
example {α β γ : Type} (P : α → β → γ → Prop) (a : α) (b : β) (c : γ) (h : P a b c) :
    ∃ x y z, P x y z := by
  use a, b
  exact ⟨c, h⟩

/-! ### R6. `⟨a⟩ : WithDim d ℝ` · a number tagged with dimension `d`; Lean prints it `{ val := a }`
`{ val := a }.val` is just `a` (`dsimp only` or `simp` reduces it). `m.1` is the same as `m.val`. -/
example {d : Dimension LTMCTDimensionBase} (a : ℝ) (P : ℝ → Prop) (h : P a) :
    P (⟨a⟩ : WithDim d ℝ).val := by
  dsimp only
  exact h

/-! ### R7. `unfold D` · goal: the defined name `D` (applied to arguments) → its body -/
def Rel (k x y : ℝ) : Prop := y = k * x
example (k a b : ℝ) (P : Prop → Prop) (h : P (b = k * a)) : P (Rel k a b) := by
  unfold Rel
  exact h

/-! ## Computing the rescaled numbers (`norm_num [...]` does R8–R15 in one call) -/

/-! ### R8. `scaleUnit_apply_fun_left` · goal: rescaling a `Prop`-valued function only rescales its input
`Prop` has no units, so `scaleUnit u1 u2 f m` is `f (scaleUnit u2 u1 m)`. A `simp` lemma. -/
example {M1 : Type} [UnitDependent M1] (u1 u2 : LTMCTUnitChoices) (f : M1 → Prop) (m : M1)
    (h : f (scaleUnit u2 u1 m)) : scaleUnit u1 u2 f m := by
  rw [scaleUnit_apply_fun_left]
  exact h

/-! ### R9. `WithDim.scaleUnit_val` · goal: value of a rescaled quantity → scale factor `•` value -/
example {d : Dimension LTMCTDimensionBase} (u1 u2 : LTMCTUnitChoices) (m : WithDim d ℝ)
    (P : ℝ → Prop) (h : P ((u1.dimScale u2) d • m.val)) : P (scaleUnit u1 u2 m).val := by
  rw [WithDim.scaleUnit_val]
  exact h

/-! ### R10. `dimScale_SIPrimed_SI` · goal: the factor from `SIPrimed` to `SI` → `2^ℓ 3^t 5^m 7^q 11^θ`
A `simp` lemma; `dimScale_SI_SIPrimed` is the other direction (`2⁻¹, 3⁻¹, …`). -/
example (d : Dimension LTMCTDimensionBase) (P : NNReal → Prop)
    (h : P (2 ^ (d.length : ℝ) * 3 ^ (d.time : ℝ) * 5 ^ (d.mass : ℝ) * 7 ^ (d.charge : ℝ) *
      11 ^ (d.temperature : ℝ))) : P (SIPrimed.dimScale SI d) := by
  rw [dimScale_SIPrimed_SI]
  exact h

/-! ### R11. `simp only [M𝓭, L𝓭, T𝓭]` · goal: the base dimensions → their exponent vectors
`ofLTMCTDimensionBase ℓ t m q θ` has exponents (length, time, mass, charge, temperature). -/
example (P : Dimension LTMCTDimensionBase → Prop)
    (h : P (ofLTMCTDimensionBase 1 0 0 0 0 * (ofLTMCTDimensionBase 0 1 0 0 0)⁻¹)) :
    P (L𝓭 * T𝓭⁻¹) := by
  simp only [L𝓭, T𝓭]
  exact h

/-! ### R12. `length_mul`, `inv_length`, `ofLTMCTDimensionBase_length` · goal: exponent of a product
Exponents add under `*` and negate under `⁻¹`; the same for `time`, `mass`, …  All are `simp` lemmas. -/
example (a b : ℚ) (P : ℚ → Prop) (h : P (1 + -1)) :
    P (ofLTMCTDimensionBase 1 0 0 0 0 * (ofLTMCTDimensionBase 1 a b 0 0)⁻¹).length := by
  simp only [length_mul, inv_length, ofLTMCTDimensionBase_length]
  exact h

/-! ### R13. `NNReal.smul_def` · `c • x = ↑c • x` for `c : NNReal` · goal: the scale factor becomes a real -/
example (c : NNReal) (x : ℝ) (P : ℝ → Prop) (h : P ((c : ℝ) • x)) : P (c • x) := by
  rw [NNReal.smul_def]
  exact h

/-! ### R14. `norm_num` · goal: numerals with real exponents and casts → one number -/
example (c : ℝ) (P : ℝ → Prop) (h : P (20 / 9 * c)) :
    P (((2 : NNReal) ^ ((1 : ℝ) + 1) * (3 : NNReal) ^ ((-1 : ℝ) + -1) * 5 : NNReal) * c) := by
  norm_num
  exact h

/-! ### R15. `eq_iff_iff`, `iff_true` · goal: an equation of propositions `A = True` → `A`
`norm_num` applies them by itself. -/
example (A : Prop) (P : Prop → Prop) (h : P A) : P (A = True) := by
  simp only [eq_iff_iff, iff_true]
  exact h

/-! ## Closing: `¬ (a * c = c * b)` with numerals `a ≠ b` and `c ≠ 0` -/

/-! ### R16. `intro h` on `¬ A` · `¬ A` is `A → False`: context gains `h : A`, goal becomes `False` -/
example (A : Prop) (h0 : A → False) : ¬ A := by
  intro h
  exact h0 h

/-! ### R17. `apply hab` with `hab : a ≠ b` · `a ≠ b` is `a = b → False`: goal `False` → `a = b` -/
example {α : Type} (a b : α) (hab : a ≠ b) (h : a = b) : False := by
  apply hab
  exact h

/-! ### R18. `linarith` · closes a linear (in)equation over `ℝ` from the hypotheses -/
example (k : ℝ) (h : 3 * k = k * 2) : k = 0 := by linarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. "momentum = mass" is not dimensionally correct: R1–R3, R5–R7, then `norm_num` (R8–R15)
A two-argument relation needs only R1–R3; with a third argument R4 is needed to get past the middle one. -/
def MomWrong (m : WithDim M𝓭 ℝ) (p : WithDim (M𝓭 * L𝓭 * T𝓭⁻¹) ℝ) : Prop := p.1 = m.1

example : ¬ IsDimensionallyCorrect MomWrong := by
  simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff]
  use SI, SIPrimed, ⟨1⟩, ⟨1⟩
  unfold MomWrong
  norm_num [WithDim.scaleUnit_val, M𝓭, L𝓭, T𝓭, NNReal.smul_def]

/-! ### W2. The closing pattern: R16 → R17 → R18 -/
example (k : ℝ) (hk : k ≠ 0) : ¬ (3 * k = k * 2) := by
  intro h
  apply hk
  linarith

end M189Guide

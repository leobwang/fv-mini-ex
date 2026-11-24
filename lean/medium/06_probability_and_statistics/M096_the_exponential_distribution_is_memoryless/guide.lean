/- Guide for M096 (The exponential distribution is memoryless).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the cdf instead of the tail,
abstract exponents, an arbitrary measure).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M096Guide

/-! # Part R · Reference entries -/

/-! ## Part 1: the tail `P(T > x)` -/

/-! ### R1. `haveI := isProbabilityMeasure_expMeasure hr` · context gains the instance `this`
Lemmas about probability measures ask for `[IsProbabilityMeasure μ]`; `haveI` puts it where
instance search finds it. (`measure_univ : μ univ = 1` only finishes the example; it needs the instance.) -/
example (r : ℝ) (hr : 0 < r) : expMeasure r Set.univ = 1 := by
  haveI := isProbabilityMeasure_expMeasure hr
  exact measure_univ

/-! ### R2. `Set.compl_Iic` · `(Iic a)ᶜ = Ioi a`; right to left: `rw [← Set.compl_Iic]` · goal -/
example {α : Type} [LinearOrder α] (a : α) (P : Set α → Prop) (h : P (Set.Iic a)ᶜ) :
    P (Set.Ioi a) := by
  rw [← Set.compl_Iic]
  exact h

/-! ### R3. `prob_compl_eq_one_sub` · `MeasurableSet s → μ sᶜ = 1 - μ s` · goal, plus side goal
Write `rw [prob_compl_eq_one_sub hs]` to supply the side goal on the spot. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hs : MeasurableSet s) (P : ENNReal → Prop) (h : P (1 - μ s)) : P (μ sᶜ) := by
  rw [prob_compl_eq_one_sub]
  exact h
  exact hs

/-! ### R4. `measurableSet_Iic` · closes `MeasurableSet (Set.Iic a)` -/
example (a : ℝ) : MeasurableSet (Set.Iic a) := by
  exact measurableSet_Iic

/-! ### R5. `ofReal_cdf` · `ENNReal.ofReal (cdf μ x) = μ (Iic x)`; right to left · goal
`↑(cdf μ) x` is how Lean prints `cdf μ x`: `cdf μ` is a `StieltjesFunction`, coerced to `ℝ → ℝ`. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) (P : ENNReal → Prop)
    (h : P (ENNReal.ofReal (cdf μ x))) : P (μ (Set.Iic x)) := by
  rw [← ofReal_cdf]
  exact h

/-! ### R6. `cdf_expMeasure_eq` · `0 < r → cdf (expMeasure r) x = if 0 ≤ x then 1 - exp (-(r * x)) else 0` -/
example (r x : ℝ) (hr : 0 < r) (P : ℝ → Prop)
    (h : P (if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0)) : P (cdf (expMeasure r) x) := by
  rw [cdf_expMeasure_eq hr]
  exact h

/-! ### R7. `if_pos` · `c → (if c then a else b) = a` · goal -/
example {α : Type} (c : Prop) [Decidable c] (hc : c) (a b : α) (P : α → Prop) (h : P a) :
    P (if c then a else b) := by
  rw [if_pos hc]
  exact h

/-! ### R8. `ENNReal.ofReal_one` · `ENNReal.ofReal 1 = 1`; right to left: `rw [← ENNReal.ofReal_one]` · goal -/
example (P : ENNReal → Prop) (h : P (ENNReal.ofReal 1)) : P 1 := by
  rw [← ENNReal.ofReal_one]
  exact h

/-! ### R9. `ENNReal.ofReal_sub` · `0 ≤ q → ofReal (p - q) = ofReal p - ofReal q`; right to left · goal -/
example (p q : ℝ) (hq : 0 ≤ q) (P : ENNReal → Prop) (h : P (ENNReal.ofReal (p - q))) :
    P (ENNReal.ofReal p - ENNReal.ofReal q) := by
  rw [← ENNReal.ofReal_sub p hq]
  exact h

/-! ### R10. `sub_nonneg` · `0 ≤ a - b ↔ b ≤ a`; `.mpr` uses it right to left · goal -/
example {α : Type} [AddGroup α] [LE α] [AddRightMono α] (a b : α) (h : b ≤ a) : 0 ≤ a - b := by
  apply sub_nonneg.mpr
  exact h

/-! ### R11. `Real.exp_le_one_iff` · `exp x ≤ 1 ↔ x ≤ 0` · goal -/
example (x : ℝ) (h : x ≤ 0) : Real.exp x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact h

/-! ### R12. `nlinarith` · closes an inequality that follows from the hypotheses by multiplying them -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : -(a * b) ≤ 0 := by
  nlinarith

/-! ### R13. `congr 1` · goal `f a = f b` → `a = b` (strips one function application) -/
example (a b : ℝ) : ENNReal.ofReal (a + b) = ENNReal.ofReal (b + a) := by
  congr 1
  ring

/-! ## Part 2: memorylessness -/

/-! ### R14. `cond_apply` · `MeasurableSet s → μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (hs : MeasurableSet s)
    (P : ENNReal → Prop) (h : P ((μ s)⁻¹ * μ (s ∩ t))) : P μ[t | s] := by
  rw [cond_apply hs]
  exact h

/-! ### R15. `measurableSet_Ioi` · closes `MeasurableSet (Set.Ioi a)` -/
example (a : ℝ) : MeasurableSet (Set.Ioi a) := by
  exact measurableSet_Ioi

/-! ### R16. `Set.Ioi_inter_Ioi` · `Ioi a ∩ Ioi b = Ioi (max a b)` · goal -/
example {α : Type} [LinearOrder α] (a b : α) (P : Set α → Prop) (h : P (Set.Ioi (max a b))) :
    P (Set.Ioi a ∩ Set.Ioi b) := by
  rw [Set.Ioi_inter_Ioi]
  exact h

/-! ### R17. `max_eq_right` · `a ≤ b → max a b = b` · goal -/
example {α : Type} [LinearOrder α] (a b : α) (hab : a ≤ b) (P : α → Prop) (h : P b) :
    P (max a b) := by
  rw [max_eq_right hab]
  exact h

/-! ### R18. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  linarith

/-! ### R19. `ENNReal.ofReal_inv_of_pos` · `0 < x → ofReal x⁻¹ = (ofReal x)⁻¹`; right to left · goal -/
example (x : ℝ) (hx : 0 < x) (P : ENNReal → Prop) (h : P (ENNReal.ofReal x⁻¹)) :
    P (ENNReal.ofReal x)⁻¹ := by
  rw [← ENNReal.ofReal_inv_of_pos hx]
  exact h

/-! ### R20. `Real.exp_pos` · `0 < exp x` · closes the goal -/
example (x : ℝ) : 0 < Real.exp x := by
  exact Real.exp_pos x

/-! ### R21. `ENNReal.ofReal_mul` · `0 ≤ p → ofReal (p * q) = ofReal p * ofReal q`; right to left · goal -/
example (p q : ℝ) (hp : 0 ≤ p) (P : ENNReal → Prop) (h : P (ENNReal.ofReal (p * q))) :
    P (ENNReal.ofReal p * ENNReal.ofReal q) := by
  rw [← ENNReal.ofReal_mul hp]
  exact h

/-! ### R22. `positivity` · closes `0 ≤ e` or `0 < e` by the shape of `e` (exp, squares, inverses …) -/
example (x : ℝ) : 0 ≤ (Real.exp x)⁻¹ := by
  positivity

/-! ### R23. `Real.exp_neg` · `exp (-x) = (exp x)⁻¹`; right to left: `rw [← Real.exp_neg]` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P (Real.exp (-x))) : P (Real.exp x)⁻¹ := by
  rw [← Real.exp_neg]
  exact h

/-! ### R24. `Real.exp_add` · `exp (x + y) = exp x * exp y`; right to left: `rw [← Real.exp_add]` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x + y))) : P (Real.exp x * Real.exp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R25. `congr 2` · goal `f (g a) = f (g b)` → `a = b` (strips two applications) -/
example (a b : ℝ) : ENNReal.ofReal (Real.exp (a + b)) = ENNReal.ofReal (Real.exp (b + a)) := by
  congr 2
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The cdf in `ℝ≥0∞`, `P(T ≤ y)`: R1, R5, R6, R7 -/
example (k y : ℝ) (hk : 0 < k) (hy : 0 ≤ y) :
    expMeasure k (Set.Iic y) = ENNReal.ofReal (1 - Real.exp (-(k * y))) := by
  haveI := isProbabilityMeasure_expMeasure hk
  rw [← ofReal_cdf]
  rw [cdf_expMeasure_eq hk]
  rw [if_pos hy]

/-! ### W2. Merging a quotient of exponentials into one `ofReal`: R19–R25, then `ring` -/
example (a b : ℝ) :
    (ENNReal.ofReal (Real.exp a))⁻¹ * ENNReal.ofReal (Real.exp b) = ENNReal.ofReal (Real.exp (b - a)) := by
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← Real.exp_neg]
  rw [← Real.exp_add]
  congr 2
  ring

/-! ### W3. A conditional probability of nested tails, for any measure on `ℝ`: R14–R18 -/
example (μ : Measure ℝ) (a b : ℝ) (hab : a ≤ b) :
    μ[Set.Ioi b | Set.Ioi a] = (μ (Set.Ioi a))⁻¹ * μ (Set.Ioi b) := by
  rw [cond_apply measurableSet_Ioi]
  rw [Set.Ioi_inter_Ioi]
  rw [max_eq_right (by linarith)]

/-! ### W4. Why `congr 1` before `ring`: `ring` cannot see inside `ENNReal.ofReal` -/
example (a : ℝ) : ENNReal.ofReal (1 - (1 - a)) = ENNReal.ofReal a := by
  congr 1
  ring

end M096Guide

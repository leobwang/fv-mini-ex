/- Guide for E098 (A fair die).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a coin, a three-sided die).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory

namespace E098Guide

/-! # Part R · Reference entries -/

/-! ## The measure of one point -/

/-! ### R1. `PMF.toMeasure_apply_singleton` · goal: `p.toMeasure {a}` → `p a`, plus side goal `MeasurableSet {a}`
Pass the side goal's proof as the third argument to skip it: `rw [PMF.toMeasure_apply_singleton p a hm]`. -/
example {α : Type} [MeasurableSpace α] (p : PMF α) (a : α) (P : ENNReal → Prop) (h : P (p a))
    (hm : MeasurableSet {a}) : P (p.toMeasure {a}) := by
  rw [PMF.toMeasure_apply_singleton p a]
  exact h
  exact hm

/-! ### R2. `measurableSet_singleton` · goal list: closes the goal `MeasurableSet {a}` -/
example {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    MeasurableSet {a} := by
  exact measurableSet_singleton a

/-! ### R3. `PMF.uniformOfFintype_apply` · goal: the uniform PMF at `a` → `(card α)⁻¹` -/
example {α : Type} [Fintype α] [Nonempty α] (a : α) (P : ENNReal → Prop)
    (h : P (Fintype.card α : ENNReal)⁻¹) : P (PMF.uniformOfFintype α a) := by
  rw [PMF.uniformOfFintype_apply]
  exact h

/-! ### R4. `Fintype.card_fin` · goal: `Fintype.card (Fin n)` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Fintype.card (Fin n)) := by
  rw [Fintype.card_fin]
  exact h

/-! ### R5. `Nat.cast_ofNat` · goal: a natural numeral cast into another type → that type's numeral -/
example (P : ENNReal → Prop) (h : P 5) : P ((5 : ℕ) : ENNReal) := by
  rw [Nat.cast_ofNat]
  exact h

/-! ## An integral over a finite type -/

/-! ### R6. `PMF.integral_eq_sum` · goal: `∫ a, f a ∂p.toMeasure` → `∑ a, (p a).toReal • f a` -/
example {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] (p : PMF α)
    (f : α → ℝ) (P : ℝ → Prop) (h : P (∑ a, (p a).toReal • f a)) : P (∫ a, f a ∂p.toMeasure) := by
  rw [PMF.integral_eq_sum]
  exact h

/-! ### R7. `ENNReal.toReal_inv` · goal: `toReal` moves inside `_⁻¹` -/
example (a : ENNReal) (P : ℝ → Prop) (h : P a.toReal⁻¹) : P (a⁻¹).toReal := by
  rw [ENNReal.toReal_inv]
  exact h

/-! ### R8. `ENNReal.toReal_ofNat` · goal: `toReal` of a numeral `≥ 2` → the real numeral -/
example (P : ℝ → Prop) (h : P 5) : P (5 : ENNReal).toReal := by
  rw [ENNReal.toReal_ofNat]
  exact h

/-! ### R9. `smul_eq_mul` · goal: `a • b` with both sides in the same type → `a * b` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ## A sum over `Fin (n + 1)` -/

/-! ### R10. `Fin.sum_univ_succ` · goal: peel off the term `i = 0` -/
example {M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M) (P : M → Prop)
    (h : P (f 0 + ∑ i : Fin n, f i.succ)) : P (∑ i, f i) := by
  rw [Fin.sum_univ_succ]
  exact h

/-! ### R11. `Fin.val_succ` · goal: the value of `j.succ` → value of `j` plus one -/
example (n : ℕ) (j : Fin n) (P : ℕ → Prop) (h : P (↑j + 1)) : P ↑j.succ := by
  rw [Fin.val_succ]
  exact h

/-! ### R12. `Fin.val_zero` · goal: the value of `0 : Fin (n + 1)` → `0 : ℕ` -/
example (n : ℕ) (P : ℕ → Prop) (h : P 0) : P ((0 : Fin (n + 1)) : ℕ) := by
  rw [Fin.val_zero]
  exact h

/-! ### R13. `Nat.cast_add`, `Nat.cast_one` · goal: the cast `ℕ → ℝ` moves inside `+` and `1` -/
example (m : ℕ) (P : ℝ → Prop) (h : P (↑m + 1)) : P ((m + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_add]
  rw [Nat.cast_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A fair coin: R1 with R2 as its third argument, then R3; `simp` evaluates `card Bool` -/
example (b : Bool) : (PMF.uniformOfFintype Bool).toMeasure {b} = 2⁻¹ := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  rw [PMF.uniformOfFintype_apply]
  simp

/-! ### W2. One weight of a three-sided die, as a real number: R3, R4, R5, R7, R8 -/
example (a : Fin 3) : ((PMF.uniformOfFintype (Fin 3)) a).toReal = 3⁻¹ := by
  rw [PMF.uniformOfFintype_apply]
  rw [Fintype.card_fin]
  rw [Nat.cast_ofNat]
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_ofNat]

/-! ### W3. The mean face of a three-sided die with faces `0, 1, 2`: R6, then `simp` with R10 -/
example : ∫ a, ((a : ℕ) : ℝ) ∂(PMF.uniformOfFintype (Fin 3)).toMeasure = 1 := by
  rw [PMF.integral_eq_sum]
  simp [Fin.sum_univ_succ]
  norm_num

end E098Guide

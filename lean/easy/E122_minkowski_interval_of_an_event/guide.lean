/- Guide for E122 (Minkowski interval of an event).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the event `r`, the number `√9`).
Assumed: Lean basics (E001–E033).

Vocabulary (physlib, via `import Physlib.Relativity.Special.ProperTime`):
* `Fin n` is the type of naturals `0, …, n - 1`. `α ⊕ β` (`Sum α β`) is the disjoint union: its elements
  are `Sum.inl a` (`a : α`) and `Sum.inr b` (`b : β`).
* `Lorentz.Vector d` is by definition `Fin 1 ⊕ Fin d → ℝ`: a function from indices to reals. The index
  `Sum.inl 0` is the time coordinate `ct`; `Sum.inr i` (with `i : Fin d`) is the spatial coordinate `i`.
* `SpaceTime d` is a reducible synonym for `Lorentz.Vector d` (`d` defaults to 3).
* `⟪x, y⟫ₘ` is `minkowskiProduct x y`, signature (+,−,−,−). `minkowskiProduct` is a bilinear map
  (type `Lorentz.Vector d →L[ℝ] Lorentz.Vector d →L[ℝ] ℝ`, `→L[ℝ]` = continuous ℝ-linear map), so the
  infoview prints `⟪x, y⟫ₘ` as `(minkowskiProduct x) y`.
* `SpaceTime.properTime x y` is `√⟪y - x, y - x⟫ₘ`, where `√` is `Real.sqrt`.
-/
import Physlib.Relativity.Special.ProperTime

open Lorentz Vector

namespace E122Guide

/-! # Part R · Reference entries -/

/-! ## The Minkowski product in coordinates -/

/-! ### R1. `rw [minkowskiProduct_toCoord]` · goal: `⟪x, y⟫ₘ` → time part minus spatial sum
`Lorentz.Vector.minkowskiProduct_toCoord : ⟪x, y⟫ₘ = x (inl 0) * y (inl 0) - ∑ i, x (inr i) * y (inr i)`. -/
example {d : ℕ} (x y : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P (x (Sum.inl 0) * y (Sum.inl 0) - ∑ i, x (Sum.inr i) * y (Sum.inr i))) : P ⟪x, y⟫ₘ := by
  rw [minkowskiProduct_toCoord]
  exact h

/-! ### R2. `Fin.sum_univ_three` · goal: a sum over `Fin 3` → three terms -/
example {M : Type} [AddCommMonoid M] (f : Fin 3 → M) (P : M → Prop) (h : P (f 0 + f 1 + f 2)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_three]
  exact h

/-! ### R3. `simp only [q]` on `q c` · goal: a `fun | … =>` definition applied to a concrete index → its value
Works only when the index is a concrete constructor such as `Sum.inr 2`, not a bound variable (W2). -/
def q : Lorentz.Vector 3 := fun
  | Sum.inl 0 => 2
  | Sum.inr _ => 1

example (P : ℝ → Prop) (h : P 2) : P (q (Sum.inl 0)) := by
  simp only [q]
  exact h

example (P : ℝ → Prop) (h : P 1) : P (q (Sum.inr 2)) := by
  simp only [q]
  exact h

/-! ### R4. `norm_num` · closes a goal of real-number arithmetic on numerals -/
example : (2 : ℝ) * 2 - 1 * 1 = 3 := by norm_num

/-! ## Proper time and square roots -/

/-! ### R5. `rw [SpaceTime.properTime]` · goal: unfold `properTime x y` → `√⟪y - x, y - x⟫ₘ` -/
example {d : ℕ} (x y : SpaceTime d) (P : ℝ → Prop) (h : P (√⟪y - x, y - x⟫ₘ)) :
    P (SpaceTime.properTime x y) := by
  rw [SpaceTime.properTime]
  exact h

/-! ### R6. `sub_zero` · `a - 0 = a` · goal: drop a subtracted zero (here the origin `0 : SpaceTime d`) -/
example {d : ℕ} (y : SpaceTime d) (P : SpaceTime d → Prop) (h : P y) : P (y - 0) := by
  rw [sub_zero]
  exact h

/-! ### R7. `rw [show (a : ℝ) = e by norm_num]` · goal: a numeral `a` → another form `e` of it
`show T by tac` is a proof of `T` written inline; the type ascription `(a : ℝ)` is required. -/
example (P : ℝ → Prop) (h : P (3 ^ 2)) : P 9 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
  exact h

/-! ### R8. `Real.sqrt_sq` · `0 ≤ x → √(x ^ 2) = x` · goal: `√(x ^ 2)` → `x` -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (√(x ^ 2)) := by
  rw [Real.sqrt_sq hx]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The coordinate chain on the event `r = (ct, x, y, z) = (3, 0, 2, 0)`: R1, R2, R3, R4 -/
def r : Lorentz.Vector 3 := fun
  | Sum.inl 0 => 3
  | Sum.inr 1 => 2
  | Sum.inr _ => 0

example : ⟪r, r⟫ₘ = 5 := by
  rw [minkowskiProduct_toCoord]
  rw [Fin.sum_univ_three]
  simp only [r]
  norm_num

/-! ### W2. Without R2, `simp [r]` is stuck on `match Sum.inr x with …` (`x` is a bound variable);
R2 afterwards makes the indices concrete, and `simp` finishes reading them off -/
example : ⟪r, r⟫ₘ = 5 := by
  rw [minkowskiProduct_toCoord]
  simp [r]
  rw [Fin.sum_univ_three]
  simp
  norm_num

/-! ### W3. `√9 = 3`: R7, then R8 closed by `exact` with `(by norm_num)` for `0 ≤ 3` -/
example : √(9 : ℝ) = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

end E122Guide

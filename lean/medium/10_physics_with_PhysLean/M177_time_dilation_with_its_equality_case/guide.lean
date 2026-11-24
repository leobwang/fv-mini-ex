/- Guide for M177 (Time dilation, with its equality case).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. A hypothesis `k` or `h` in an entry is only there to finish the example; it shows what
the goal or hypothesis became. `G : Prop` is a goal the entry does not touch.
Part W: worked combinations on objects that are NOT the exercise's (a plain `f : Fin n → ℝ`, reals
`x y`, `√(a ^ 2 - s)`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.Special.ProperTime

open Lorentz Vector

namespace M177Guide

/-! # Part R · Reference entries -/

/-! ## Proper time → a square root of coordinates -/

/-! ### R1. `unfold SpaceTime.properTime` · goal: `q.properTime p` → `√⟪p - q, p - q⟫ₘ`
`⟪x, y⟫ₘ` prints as `(minkowskiProduct x) y`. -/
example {d : ℕ} (q p : SpaceTime d) (P : ℝ → Prop) (h : P √⟪p - q, p - q⟫ₘ) :
    P (SpaceTime.properTime q p) := by
  unfold SpaceTime.properTime
  exact h

/-! ### R2. `set v := e with hv` · context gains `v := e` and `hv : v = e`; goal: every `e` → `v` -/
example {d : ℕ} (q p : SpaceTime d) (P : SpaceTime d → Prop) (k : ∀ w, P w) : P (p - q) := by
  set v := p - q with hv
  exact k v

/-! ### R3. `minkowskiProduct_toCoord` · goal: `⟪x, y⟫ₘ` → time product minus the sum of space products -/
example {d : ℕ} (x y : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P (x (Sum.inl 0) * y (Sum.inl 0) - ∑ i, x (Sum.inr i) * y (Sum.inr i))) : P ⟪x, y⟫ₘ := by
  rw [minkowskiProduct_toCoord]
  exact h

/-! ### R4. `sq` · `a ^ 2 = a * a`; `simp only [sq]` rewrites every square, also under `∑` -/
example {n : ℕ} (a : ℝ) (f : Fin n → ℝ) (P : ℝ → Prop) (h : P (a * a - ∑ i, f i * f i)) :
    P (a ^ 2 - ∑ i, f i ^ 2) := by
  simp only [sq]
  exact h

/-! ## Signs of sums of squares -/

/-! ### R5. `sq_nonneg` · `0 ≤ a ^ 2` · context gains the fact -/
example (a : ℝ) (G : Prop) (k : 0 ≤ a ^ 2 → G) : G := by
  have h := sq_nonneg a
  exact k h

/-! ### R6. `Finset.sum_nonneg` · `(∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i` · goal: a sum → its terms
`∑ i, f i` is `∑ i ∈ Finset.univ, f i`: the sum over every `i : Fin n`. -/
example {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) : 0 ≤ ∑ i, f i := by
  apply Finset.sum_nonneg
  intro i _
  exact hf i

/-! ## Splitting `A ∧ (B ↔ C)` -/

/-! ### R7. `refine ⟨?_, ⟨fun hb => ?_, fun hc => ?_⟩⟩` · goal list: one goal → three
An `↔` is built like a pair: `⟨proof of →, proof of ←⟩`. -/
example (A B C : Prop) (ha : A) (hbc : B → C) (hcb : C → B) : A ∧ (B ↔ C) := by
  refine ⟨?_, ⟨fun hb => ?_, fun hc => ?_⟩⟩
  · exact ha
  · exact hbc hb
  · exact hcb hc

/-! ## Square roots and inequalities -/

/-! ### R8. `h.le` (lemma `le_of_lt`) · `a < b → a ≤ b` · context gains the weak inequality -/
example (a b : ℝ) (h : a < b) (G : Prop) (k : a ≤ b → G) : G := by
  have h' := h.le
  exact k h'

/-! ### R9. `Real.sqrt_le_left` · `0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)` · goal: `√x ≤ y` → `x ≤ y ^ 2` -/
example (x y : ℝ) (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y := by
  rw [Real.sqrt_le_left hy]
  exact h

/-! ### R10. `linarith` · closes a linear (in)equality that follows from the hypotheses
It treats `a ^ 2`, `∑ …`, `⟪v, v⟫ₘ` as opaque atoms. -/
example (x a s : ℝ) (hx : x = a - s) (hs : 0 ≤ s) : x ≤ a := by
  linarith

/-! ### R11. `by_contra hneg` · goal `G` → `False`; context gains `hneg : ¬G` -/
example (x : ℝ) (k : ¬0 ≤ x → False) : 0 ≤ x := by
  by_contra hneg
  exact k hneg

/-! ### R12. `not_le` · `¬a ≤ b ↔ b < a`; `.mp` turns a hypothesis `¬a ≤ b` into `b < a` -/
example (a b : ℝ) (h : ¬a ≤ b) (G : Prop) (k : b < a → G) : G := by
  have h' := not_le.mp h
  exact k h'

/-! ### R13. `Real.sqrt_eq_zero'` · `√x = 0 ↔ x ≤ 0` · context: `√x` in `h` → `0` (via `.mpr hx`) -/
example (x : ℝ) (hx : x ≤ 0) (P : ℝ → Prop) (h : P √x) (G : Prop) (k : P 0 → G) : G := by
  rw [Real.sqrt_eq_zero'.mpr hx] at h
  exact k h

/-! ### R14. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · goal: `√x ^ 2` → `x` -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! ## A zero sum of squares → zero terms -/

/-! ### R15. `Finset.sum_eq_zero_iff_of_nonneg` · nonnegative terms: `∑ = 0 ↔ every term = 0` · goal
With `rw` the goal changes; forwards, `(… hf).mp hz` turns `hz : ∑ i, f i = 0` into the right side. -/
example {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i ∈ Finset.univ, 0 ≤ f i)
    (h : ∀ i ∈ Finset.univ, f i = 0) : ∑ i, f i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg hf]
  exact h

/-! ### R16. `Finset.mem_univ` · `i ∈ Finset.univ` · goal list: closes the `∈ Finset.univ` premise -/
example {n : ℕ} (f : Fin n → ℝ) (i : Fin n) (h : ∀ j ∈ Finset.univ, f j = 0) : f i = 0 := by
  apply h
  exact Finset.mem_univ i

/-! ### R17. `pow_eq_zero_iff two_ne_zero` · `a ^ 2 = 0 ↔ a = 0` · context gains `a = 0`
`two_ne_zero : 2 ≠ 0` is the premise `n ≠ 0` of `pow_eq_zero_iff`. -/
example (a : ℝ) (h : a ^ 2 = 0) (G : Prop) (k : a = 0 → G) : G := by
  have h' := (pow_eq_zero_iff two_ne_zero).mp h
  exact k h'

/-! ## From `v` back to `p` and `q` -/

/-! ### R18. `Lorentz.Vector.apply_sub` · context: component of a difference → difference of components -/
example {d : ℕ} (x y : Lorentz.Vector d) (μ : Fin 1 ⊕ Fin d) (P : ℝ → Prop) (h : P ((x - y) μ))
    (G : Prop) (k : P (x μ - y μ) → G) : G := by
  rw [Lorentz.Vector.apply_sub] at h
  exact k h

/-! ### R19. `sub_eq_zero` · `a - b = 0 ↔ a = b` · context: `h : a - b = 0` → `h : a = b` -/
example (a b : ℝ) (h : a - b = 0) (G : Prop) (k : a = b → G) : G := by
  rw [sub_eq_zero] at h
  exact k h

/-! ### R20. `simpa [lemmas] using h` · closes the goal: simplifies `h` and the goal with the same
lemmas, then `h` closes the goal. Give it `hv` from R2 to turn `v` back into `p - q`. -/
example {d : ℕ} (x y w : Lorentz.Vector d) (hw : w = x - y) (μ : Fin 1 ⊕ Fin d) (h : w μ = 0) :
    x μ = y μ := by
  simpa [hw, sub_eq_zero] using h

/-! ## The equality case, backwards -/

/-! ### R21. `Finset.sum_eq_zero` · `(∀ i ∈ s, f i = 0) → ∑ i ∈ s, f i = 0` · goal: a sum → its terms -/
example {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, f i = 0) : ∑ i, f i = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact hf i

/-! ### R22. `sub_zero` · `a - 0 = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a - 0) := by
  rw [sub_zero]
  exact h

/-! ### R23. `Real.sqrt_sq` · `0 ≤ a → √(a ^ 2) = a` · goal: `√(a ^ 2)` → `a` -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h : P a) : P √(a ^ 2) := by
  rw [Real.sqrt_sq ha]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A zero sum of squares has zero terms: R5 inside R15, then R16, R17 -/
example {n : ℕ} (f : Fin n → ℝ) (hz : ∑ i, f i ^ 2 = 0) (i : Fin n) : f i = 0 := by
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f j))).mp hz i
    (Finset.mem_univ i)
  exact (pow_eq_zero_iff two_ne_zero).mp h3

/-! ### W2. Squaring an equation `√x = y`: `rw [← he]`, then R14 -/
example (x y : ℝ) (hx : 0 ≤ x) (he : √x = y) : x = y ^ 2 := by
  rw [← he]
  rw [Real.sq_sqrt hx]

/-! ### W3. `√x = y` with `y > 0` forces `0 ≤ x`: R11, R12, R8, R13 at `he`, R10 -/
example (x y : ℝ) (hy : 0 < y) (he : √x = y) : 0 ≤ x := by
  by_contra hneg
  rw [Real.sqrt_eq_zero'.mpr (not_le.mp hneg).le] at he
  linarith

/-! ### W4. A square root that collapses: `rw [hs]`, R22, R23 -/
example (a s : ℝ) (ha : 0 ≤ a) (hs : s = 0) : √(a ^ 2 - s) = a := by
  rw [hs]
  rw [sub_zero]
  rw [Real.sqrt_sq ha]

end M177Guide

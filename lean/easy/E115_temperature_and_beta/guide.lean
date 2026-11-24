/- Guide for E115 (Temperature and β).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `g` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.Thermodynamics.Temperature.Basic

open Constants

namespace E115Guide

/-! # Part R · Reference entries -/

/-! ## From `β` to a formula in ℝ -/

/-! ### R1. `Temperature.β_toReal` · `(T.β : ℝ) = 1 / (kB * T.toReal)` · goal
`T.β : ℝ≥0`; the cast `↑T.β : ℝ` is rewritten to its defining formula. -/
example (T : Temperature) (P : ℝ → Prop) (h : P (1 / (kB * T.toReal))) : P (T.β : ℝ) := by
  rw [Temperature.β_toReal]
  exact h

/-! ## Moving facts from `ℝ≥0` to `ℝ`, and adding `0 < kB` -/

/-! ### R2. `have h : (0 : ℝ) < T.toReal := hT` · context gains the ℝ version of `hT : 0 < T.val`
`T.toReal` is by definition `↑T.val`, and `<` on `ℝ≥0` is by definition `<` of the casts, so `hT`
itself proves the ℝ statement. The named lemma is `NNReal.coe_pos : 0 < ↑r ↔ 0 < r`. -/
example (T : Temperature) (hT : 0 < T.val) (G : Prop) (g : (0 : ℝ) < T.toReal → G) : G := by
  have h : (0 : ℝ) < T.toReal := hT
  exact g h

/-! ### R3. `have h : T₁.toReal < T₂.toReal := hlt` · context gains the ℝ version of `T₁.val < T₂.val`
Same reason as R2. The named lemma is `NNReal.coe_lt_coe : ↑r₁ < ↑r₂ ↔ r₁ < r₂`. -/
example (T₁ T₂ : Temperature) (hlt : T₁.val < T₂.val) (G : Prop)
    (g : T₁.toReal < T₂.toReal → G) : G := by
  have h : T₁.toReal < T₂.toReal := hlt
  exact g h

/-! ### R4. `Constants.kB_pos : 0 < kB` · context gains `hk : 0 < kB`
`kB : ℝ` is Boltzmann's constant (`open Constants` lets you write `kB`, `kB_pos`). -/
example (G : Prop) (g : 0 < kB → G) : G := by
  have hk := kB_pos
  exact g hk

/-! ## Closing the real-number goals -/

/-! ### R5. `positivity` · closes `0 < e` (or `0 ≤ e`, `e ≠ 0`) built from `*`, `/`, `+`, numerals
For a variable or an opaque term such as `T.toReal` it needs `0 < ·` as a hypothesis in context. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < 1 / (a * b) := by
  positivity

/-! ### R6. `field_simp` · clears denominators it can prove nonzero; here it closes the goal
It proves `a ≠ 0` from a hypothesis `a ≠ 0` or `0 < a` in context. -/
example (a : ℝ) (ha : 0 < a) : 1 / a * a = 1 := by
  field_simp

/-! ### R7. `gcongr` · closes `1 / y < 1 / x` by reducing it to `x < y` (main goal) and `0 < x`
(side goal). It closes a main goal that is a hypothesis, and side goals with `positivity`. -/
example (x y : ℝ) (hx : 0 < x) (hxy : x < y) : 1 / y < 1 / x := by
  gcongr

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Two temperatures in one goal: each `rw [Temperature.β_toReal]` rewrites ONE of them
`rw` fixes `T` at the first match (`T₁`) and rewrites only `↑T₁.β`; the second `rw` gets `↑T₂.β`. -/
example (T₁ T₂ : Temperature) (P : ℝ → Prop)
    (h : P (1 / (kB * T₁.toReal) + 1 / (kB * T₂.toReal))) : P ((T₁.β : ℝ) + T₂.β) := by
  rw [Temperature.β_toReal]
  rw [Temperature.β_toReal]
  exact h

/-! ### W2. Hotter means larger thermal energy `kB T`: R3, R4, then R7 -/
example (T₁ T₂ : Temperature) (hlt : T₁.val < T₂.val) : kB * T₁.toReal < kB * T₂.toReal := by
  have h : T₁.toReal < T₂.toReal := hlt
  have hk := kB_pos
  gcongr

/-! ### W3. What `gcongr` leaves when the facts are not hypotheses of their own
A fact inside `∧` is invisible to it: both goals of R7 stay open. -/
example (x y : ℝ) (h : 0 < x ∧ x < y) : 1 / y < 1 / x := by
  gcongr
  exacts [h.1, h.2]

end E115Guide

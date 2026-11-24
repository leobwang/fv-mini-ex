/- Guide for M121 (Condition number bound).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other matrices and vectors).
Assumed: Lean basics.
-/
import Mathlib

open Matrix
open scoped Matrix.Norms.Operator

namespace M121Guide

/-! # Part R · Reference entries -/

/-! ## Matrix–vector algebra (`*ᵥ` is `Matrix.mulVec`, matrix times column vector) -/

/-! ### R1. `Matrix.mulVec_sub` · `M *ᵥ (u - v) = M *ᵥ u - M *ᵥ v`; `rw [← …]` pulls `M` out · goal -/
example {α : Type} [CommRing α] {k : ℕ} (M : Matrix (Fin k) (Fin k) α) (u v : Fin k → α)
    (P : (Fin k → α) → Prop) (h : P (M *ᵥ (u - v))) : P (M *ᵥ u - M *ᵥ v) := by
  rw [← Matrix.mulVec_sub]
  exact h

/-! ### R2. `Matrix.mulVec_mulVec` · `M *ᵥ N *ᵥ v = (M * N) *ᵥ v` · goal
`*ᵥ` groups to the right: `M *ᵥ N *ᵥ v` is `M *ᵥ (N *ᵥ v)`. -/
example {α : Type} [CommRing α] {k : ℕ} (M N : Matrix (Fin k) (Fin k) α) (v : Fin k → α)
    (P : (Fin k → α) → Prop) (h : P ((M * N) *ᵥ v)) : P (M *ᵥ N *ᵥ v) := by
  rw [Matrix.mulVec_mulVec]
  exact h

/-! ### R3. `Matrix.one_mulVec` · `1 *ᵥ v = v` (`1` is the identity matrix) · goal -/
example {α : Type} [CommRing α] {k : ℕ} (v : Fin k → α) (P : (Fin k → α) → Prop) (h : P v) :
    P ((1 : Matrix (Fin k) (Fin k) α) *ᵥ v) := by
  rw [Matrix.one_mulVec]
  exact h

/-! ## Proving `u ≠ 0` -/

/-! ### R4. `rintro rfl` · goal `u ≠ 0` → `False`; context: `u` replaced by `0` everywhere
`u ≠ 0` unfolds to `u = 0 → False`; `rintro rfl` introduces the equation and substitutes it. -/
example {α : Type} [CommRing α] {k : ℕ} (M : Matrix (Fin k) (Fin k) α) (u w : Fin k → α)
    (hu : M *ᵥ u = w) (H : M *ᵥ 0 ≠ w) : u ≠ 0 := by
  rintro rfl
  exact H hu

/-! ### R5. `exact hne e` · closes `False`: `hne : a ≠ b` is a function from `a = b` to `False`
Write `exact hne (by …)` to prove `a = b` on the spot: the `by` block starts with goal `⊢ a = b`. -/
example {β : Type} (a b : β) (hne : a ≠ b) (e : a = b) : False := by
  exact hne e

/-! ### R6. `Matrix.mulVec_zero` · `M *ᵥ 0 = 0` · goal -/
example {α : Type} [CommRing α] {k : ℕ} (M : Matrix (Fin k) (Fin k) α) (P : (Fin k → α) → Prop)
    (h : P 0) : P (M *ᵥ 0) := by
  rw [Matrix.mulVec_zero]
  exact h

/-! ## Norms -/

/-! ### R7. `norm_pos_iff` · `0 < ‖a‖ ↔ a ≠ 0` · goal; as a term `norm_pos_iff.mpr ha : 0 < ‖a‖` -/
example {k : ℕ} (v : Fin k → ℝ) (hv : v ≠ 0) : 0 < ‖v‖ := by
  rw [norm_pos_iff]
  exact hv

/-! ### R8. `Matrix.linfty_opNorm_mulVec` · `‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖` · context gains the bound
Needs `open scoped Matrix.Norms.Operator`, which makes `‖M‖` the ∞-operator norm. -/
example {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) (G : Prop)
    (g : ‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖ → G) : G := by
  have hb := Matrix.linfty_opNorm_mulVec M v
  exact g hb

/-! ### R9. `h ▸ e` · a term: `e : P a` with `h : a = b` becomes a proof of `P b` (either direction)
The tactic version is `rw [h] at e` (context: `e : P a` → `e : P b`). -/
example {β : Type} (a b : β) (P : β → Prop) (h : a = b) (e : P a) : P b := h ▸ e

example {β : Type} (a b : β) (P : β → Prop) (h : a = b) (e : P a) : P b := by
  rw [h] at e
  exact e

/-! ## Inequalities with a quotient -/

/-! ### R10. `div_le_iff₀` · `0 < c → (b / c ≤ a ↔ b ≤ a * c)` · goal: multiply the denominator away -/
example (a b c : ℝ) (hc : 0 < c) (h : b ≤ a * c) : b / c ≤ a := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R11. `calc` · goal `a ≤ d` → a chain of steps, each with its own proof
`≤` then `=` then `≤` composes to `≤`; the first and last terms must match the goal. -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b = c) (h3 : c ≤ d) : a ≤ d := by
  calc a ≤ b := h1
    _ = c := h2
    _ ≤ d := h3

/-! ### R12. `field_simp` · goal: clears denominators that it can show are `≠ 0`
It looks for `hc : c ≠ 0` or `hc : 0 < c` in the context, and may reorder factors (`c * b`). -/
example (a b c d : ℝ) (hc : 0 < c) (h : a + c * b = c * d) : a / c + b = d := by
  field_simp
  exact h

/-! ### R13. `gcongr` · goal `c * a ≤ c * b` → `a ≤ b` (side goal `0 ≤ c` closed automatically)
It closes the remaining goal itself when it is a hypothesis; here it is not, so it stays. -/
example {k : ℕ} (u : Fin k → ℝ) (a b : ℝ) (h : a + 0 ≤ b) : ‖u‖ * a ≤ ‖u‖ * b := by
  gcongr
  simpa using h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Undo a left inverse inside a difference: R1, R2, `rw [hCD]`, R3 -/
example {k : ℕ} (C D : Matrix (Fin k) (Fin k) ℝ) (hCD : C * D = 1) (u v : Fin k → ℝ) :
    C *ᵥ (D *ᵥ u - D *ᵥ v) = u - v := by
  rw [← Matrix.mulVec_sub]
  rw [Matrix.mulVec_mulVec]
  rw [hCD]
  rw [Matrix.one_mulVec]

/-! ### W2. A ratio bound: R10, then the product bound R8 -/
example {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) (hv : 0 < ‖v‖) :
    ‖M *ᵥ v‖ / ‖v‖ ≤ ‖M‖ := by
  rw [div_le_iff₀ hv]
  exact Matrix.linfty_opNorm_mulVec M v

/-! ### W3. Insert `· / c * c` with `field_simp`, then enlarge one factor with `gcongr`: R11, R12, R13 -/
example {k : ℕ} (u v w : Fin k → ℝ) (hv : 0 < ‖v‖) (hw : ‖v‖ ≤ ‖w‖) :
    ‖u‖ ≤ ‖u‖ / ‖v‖ * ‖w‖ := by
  calc ‖u‖ = ‖u‖ / ‖v‖ * ‖v‖ := by field_simp
    _ ≤ ‖u‖ / ‖v‖ * ‖w‖ := by gcongr

end M121Guide

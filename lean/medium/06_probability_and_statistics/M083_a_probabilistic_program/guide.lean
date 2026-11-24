/- Guide for M083 (A probabilistic program).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (one coin, other fractions).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open scoped ENNReal

namespace M083Guide

/-! # Part R · Reference entries -/

/-! ## From a `do` block to probabilities -/

/-- A one-step program used only to demonstrate R1: draw `a` from `p`, return `f a`. -/
noncomputable def relabel {α β : Type} (p : PMF α) (f : α → β) : PMF β := do
  let a ← p
  return f a

/-! ### R1. `show T` · goal: replaced by a definitionally equal `T` (here: the name and its `do` block
spelled out as `PMF.bind` / `PMF.pure`) -/
example {α β : Type} (p : PMF α) (f : α → β) (b : β) (P : ℝ≥0∞ → Prop)
    (h : P ((p.bind fun a => PMF.pure (f a)) b)) : P (relabel p f b) := by
  show P ((p.bind fun a => PMF.pure (f a)) b)
  exact h

/-! ### R2. `PMF.bind_apply` · goal: `(p.bind f) b` → a sum over the first draw -/
example {α β : Type} (p : PMF α) (f : α → PMF β) (b : β) (P : ℝ≥0∞ → Prop)
    (h : P (∑' a, p a * f a b)) : P (p.bind f b) := by
  rw [PMF.bind_apply]
  exact h

/-! ### R3. `tsum_bool` · goal: a sum over `Bool` → two terms -/
example {α : Type} [AddCommMonoid α] [TopologicalSpace α] (f : Bool → α) (P : α → Prop)
    (h : P (f false + f true)) : P (∑' i, f i) := by
  rw [tsum_bool]
  exact h

/-! ### R4. `PMF.pure_apply` · goal: `PMF.pure a a'` → an `if`
The lemma's `if` decides `a' = a` classically, so the example writes `open Classical in` to state
the same `if` in `h`. In the exercise `simp` evaluates that `if` (R7) and you never write it. -/
open Classical in
example {α : Type} (a a' : α) (P : ℝ≥0∞ → Prop) (h : P (if a' = a then 1 else 0)) :
    P (PMF.pure a a') := by
  rw [PMF.pure_apply]
  exact h

/-! ### R5. `PMF.uniformOfFintype_apply` · goal: a uniform probability → `1 / (number of outcomes)` -/
example {α : Type} [Fintype α] [Nonempty α] (a : α) (P : ℝ≥0∞ → Prop)
    (h : P (↑(Fintype.card α))⁻¹) : P (PMF.uniformOfFintype α a) := by
  rw [PMF.uniformOfFintype_apply]
  exact h

/-! ### R6. `Fintype.card_bool` · goal: `Fintype.card Bool` → `2` -/
example (P : ℕ → Prop) (h : P 2) : P (Fintype.card Bool) := by
  rw [Fintype.card_bool]
  exact h

/-! ## Cleaning up -/

/-! ### R7. `simp` · goal: evaluates `if`s on concrete `Bool`s, then `x * 1`, `x * 0`, `+ 0` -/
example (x : ℝ≥0∞) (P : ℝ≥0∞ → Prop) (h : P x) :
    P (x * (if true = !false then 1 else 0) + x * (if true = !true then 1 else 0)) := by
  simp
  exact h

/-! ### R8. `Nat.cast_ofNat` · goal: `↑2` (the natural number 2 cast to `ℝ≥0∞`) → the literal `2` -/
example (P : ℝ≥0∞ → Prop) (h : P 2⁻¹) : P (↑(2 : ℕ))⁻¹ := by
  rw [Nat.cast_ofNat]
  exact h

/-! ### R9. `ENNReal.inv_two_add_inv_two` · goal: `2⁻¹ + 2⁻¹` → `1` in `ℝ≥0∞` -/
example (P : ℝ≥0∞ → Prop) (h : P 1) : P (2⁻¹ + 2⁻¹) := by
  rw [ENNReal.inv_two_add_inv_two]
  exact h

/-! ### R10. `mul_one` · goal: `a * 1` → `a` -/
example {α : Type} [MulOneClass α] (a : α) (P : α → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ## Moving an equation from `ℝ≥0∞` to `ℝ` -/

/-! ### R11. `rw [← ENNReal.toReal_eq_toReal_iff']` · goal `x = y` → `x.toReal = y.toReal`, plus side
goals `x ≠ ∞`, `y ≠ ∞` (goal list). Write `(by finiteness)` twice to close them on the spot. -/
example (x y : ℝ≥0∞) (hx : x ≠ ∞) (hy : y ≠ ∞) (h : x.toReal = y.toReal) : x = y := by
  rw [← ENNReal.toReal_eq_toReal_iff']
  exact h
  exact hx
  exact hy

/-! ### R12. `finiteness` · closes a goal `t ≠ ∞` built from `+`, `*`, `⁻¹` of nonzero numerals, and
variables known to be finite -/
example (a : ℝ≥0∞) (ha : a ≠ ∞) : a * 2⁻¹ + 3⁻¹ ≠ ∞ := by
  finiteness

/-! ### R13. `ENNReal.toReal_add` · goal: `(a + b).toReal` → `a.toReal + b.toReal`, plus side goals
`a ≠ ∞`, `b ≠ ∞` -/
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) (P : ℝ → Prop) (h : P (a.toReal + b.toReal)) :
    P (a + b).toReal := by
  rw [ENNReal.toReal_add]
  exact h
  exact ha
  exact hb

/-! ### R14. `ENNReal.toReal_mul` · goal: `(a * b).toReal` → `a.toReal * b.toReal` (no side goal) -/
example (a b : ℝ≥0∞) (P : ℝ → Prop) (h : P (a.toReal * b.toReal)) : P (a * b).toReal := by
  rw [ENNReal.toReal_mul]
  exact h

/-! ### R15. `ENNReal.toReal_inv` · goal: `a⁻¹.toReal` → `a.toReal⁻¹` -/
example (a : ℝ≥0∞) (P : ℝ → Prop) (h : P a.toReal⁻¹) : P a⁻¹.toReal := by
  rw [ENNReal.toReal_inv]
  exact h

/-! ### R16. `ENNReal.toReal_div` · goal: `(a / b).toReal` → `a.toReal / b.toReal` -/
example (a b : ℝ≥0∞) (P : ℝ → Prop) (h : P (a.toReal / b.toReal)) : P (a / b).toReal := by
  rw [ENNReal.toReal_div]
  exact h

/-! ### R17. `ENNReal.toReal_ofNat` · goal: `ENNReal.toReal 3` → the real literal `3` -/
example (P : ℝ → Prop) (h : P 3) : P (ENNReal.toReal 3) := by
  rw [ENNReal.toReal_ofNat]
  exact h

/-! ### R18. `norm_num` · closes a numeral identity in `ℝ` (it does not close the same one in `ℝ≥0∞`) -/
example : (2 : ℝ)⁻¹ * 3⁻¹ + 3⁻¹ = 1 / 2 := by
  norm_num

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- One fair coin, negated. -/
noncomputable def flipNot : PMF Bool := do
  let a ← PMF.uniformOfFintype Bool
  return (!a)

/-! ### W1. `show` (R1), then expand the probabilities (R2–R6), then `simp` (R7, R8) -/
example : flipNot true = 2⁻¹ := by
  show ((PMF.uniformOfFintype Bool).bind fun a => PMF.pure (!a)) true = 2⁻¹
  simp only [PMF.bind_apply, tsum_bool, PMF.pure_apply, PMF.uniformOfFintype_apply, Fintype.card_bool]
  simp

/-! ### W2. A numeral identity in `ℝ≥0∞`, moved to `ℝ` (R11, R12, R13), cast down (R15–R17), closed (R18) -/
example : (4⁻¹ + 2⁻¹ : ℝ≥0∞) = 3 / 4 := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_div]
  norm_num

end M083Guide

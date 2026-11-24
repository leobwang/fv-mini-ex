/- Guide for E066 (ε–δ binders and abs).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other bounds, other intervals).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E066Guide

/-! # Part R · Reference entries -/

/-! ## Binder predicates: `∀ ε > 0` and `∃ δ > 0` -/

/-! ### R1. `intro ε hε` on `∀ ε > 0, P ε` · context gains `ε` and `hε : ε > 0`
`∀ ε > 0, P ε` is notation for `∀ ε, ε > 0 → P ε`: two binders, so `intro` takes two names. -/
example (P : ℝ → Prop) (hP : ∀ ε, ε > 0 → P ε) : ∀ ε > (0 : ℝ), P ε := by
  intro ε hε
  exact hP ε hε

/-! ### R2. `refine ⟨d, ?_, ?_⟩` on `∃ δ > 0, Q δ` · goal → two goals `d > 0` and `Q d`
`∃ δ > 0, Q δ` is notation for `∃ δ, δ > 0 ∧ Q δ`. The anonymous constructor `⟨d, p, q⟩` flattens the
nested `∃` and `∧`: witness `d`, then a proof of `d > 0`, then a proof of `Q d`. -/
example (Q : ℝ → Prop) (d : ℝ) (hd : d > 0) (hq : Q d) : ∃ δ > 0, Q δ := by
  refine ⟨d, ?_, ?_⟩
  exact hd
  exact hq

/-! ### R3. `positivity` · closes `0 < e`, `e > 0`, `0 ≤ e` when `e` is built from positive pieces
It reads hypotheses such as `hε : ε > 0` for the variables, and knows numerals, `/`, `*`, `^`, `|·|`. -/
example (ε : ℝ) (hε : ε > 0) : ε / 5 > 0 := by
  positivity

/-! ### R4. `linarith` · closes a linear (in)equality that follows from the hypotheses
Linear: sums of constants times atoms. An atom can be any term (`ε`, `x`, `|x|`, `f x`). -/
example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ 2 * c) : a / 2 < c := by
  linarith

/-! ## Absolute value as an interval -/

/-! ### R5. `abs_sub_lt_iff` · goal: `|a - b| < c` → `a - b < c ∧ b - a < c`
`|a|` is `abs a`, typed `|a|`. -/
example {G : Type} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a b c : G)
    (h : a - b < c ∧ b - a < c) : |a - b| < c := by
  rw [abs_sub_lt_iff]
  exact h

/-! ### R6. `constructor` on `A ↔ B` · goal → two goals `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exact hab
  exact hba

/-! ### R7. `linarith [t₁, t₂]` · closes the goal using the terms `tᵢ` as extra facts
For `h : A ∧ B`, `h.1 : A` and `h.2 : B` are the two halves (`And.left`, `And.right`). -/
example (a b x : ℝ) (h : a < x ∧ x < b) : a < b := by
  linarith [h.1, h.2]

/-! ## Closed intervals and powers -/

/-! ### R8. `Set.mem_Icc` · context: `h : x ∈ Set.Icc a b` → `h : a ≤ x ∧ x ≤ b`
`Set.Icc a b` is the closed interval `[a, b] = {x | a ≤ x ∧ x ≤ b}`. The rewrite is optional:
membership unfolds to that `∧` by definition, so `h.1 : a ≤ x` and `h.2 : x ≤ b` work on `h` directly. -/
example {α : Type} [Preorder α] (a b x : α) (P : Prop) (hP : a ≤ x → P)
    (h : x ∈ Set.Icc a b) : P := by
  rw [Set.mem_Icc] at h
  exact hP h.1

/-! ### R9. `pow_le_one₀` · `0 ≤ a → a ≤ 1 → a ^ n ≤ 1`; `apply` it: goal → two goals -/
example {M₀ : Type} [MonoidWithZero M₀] [Preorder M₀] [PosMulMono M₀] (a : M₀) (n : ℕ)
    (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ n ≤ 1 := by
  apply pow_le_one₀
  exact h₀
  exact h₁

/-! ## Rewriting the bound -/

/-! ### R10. `refine fun x hx => ?_` · goal `∀ x, A x → B x` → context gains `x`, `hx`; goal `B x`
The same `fun x hx => ?_` can fill the last slot of R2: `refine ⟨d, ?_, fun x hx => ?_⟩`. -/
example {α : Type} (A B : α → Prop) (hAB : ∀ x, A x → B x) : ∀ x, A x → B x := by
  refine fun x hx => ?_
  exact hAB x hx

/-! ### R11. `rw [hf]` with `hf : ∀ x, f x = g x` · goal: `f y` → `g y`
`rw` finds the instance `x := y` by itself. -/
example (f g : ℝ → ℝ) (hf : ∀ x, f x = g x) (y : ℝ) (P : ℝ → Prop) (h : P (g y)) : P (f y) := by
  rw [hf]
  exact h

/-! ### R12. `abs_mul` · `|a * b| = |a| * |b|` -/
example {α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (a b : α) (P : α → Prop)
    (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R13. `norm_num` · goal: evaluates the absolute value of a numeral, `|(-2)|` → `2` -/
example (y ε : ℝ) (h : 2 * y < ε) : |(-2 : ℝ)| * y < ε := by
  norm_num
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `∀ ε > 0, ∃ δ > 0, …` with a witness: R1, R2, R3, R4 -/
example : ∀ ε > (0 : ℝ), ∃ δ > 0, 2 * δ < ε := by
  intro ε hε
  refine ⟨ε / 4, ?_, ?_⟩
  positivity
  linarith

/-! ### W2. One direction of an `|x - a| < r` statement: R5 on a hypothesis, then R7 -/
example (x : ℝ) (h : |x - 5| < 1) : 4 < x := by
  rw [abs_sub_lt_iff] at h
  linarith [h.1, h.2]

/-! ### W3. An interval hypothesis feeds a power lemma: R8 without the rewrite
`one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n` is the companion of R9. -/
example (x : ℝ) (h : x ∈ Set.Icc (1 : ℝ) 2) : 1 ≤ x ^ 3 := by
  exact one_le_pow₀ h.1

/-! ### W4. A bound through a product: R12, R13, R4 -/
example (x : ℝ) (hx : |x| < 1) : |(-2) * x| < 3 := by
  rw [abs_mul]
  norm_num
  linarith

end E066Guide

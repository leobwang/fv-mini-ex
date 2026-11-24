/- Guide for M164 (Ising ground state).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other spin weights, other sums).
Assumed: Lean basics.
-/
import Mathlib

namespace M164Guide

/-! # Part R · Reference entries -/

/-! ## Least elements of a range -/

/-! ### R1. `refine ⟨?_, ?_⟩` on `IsLeast s a` · goal → two goals: `a ∈ s`, `a ∈ lowerBounds s`
`IsLeast s a` is defined as `a ∈ s ∧ a ∈ lowerBounds s`: `a` is attained and is a lower bound. -/
example {α : Type} [Preorder α] (s : Set α) (a : α) (h₁ : a ∈ s) (h₂ : a ∈ lowerBounds s) :
    IsLeast s a := by
  refine ⟨?_, ?_⟩
  exacts [h₁, h₂]

/-! ### R2. `refine ⟨x, ?_⟩` on `a ∈ Set.range f` · goal → `f x = a`
`Set.range f = {f x | x}`; membership `a ∈ Set.range f` means `∃ x, f x = a`. -/
example {α β : Type} (f : α → β) (a : β) (x : α) (h : f x = a) : a ∈ Set.range f := by
  refine ⟨x, ?_⟩
  exact h

/-! ## Evaluating a configuration -/

/-! ### R3. `simp only [D]` · goal: the name `D` → its body -/
def w (b : Bool) : ℝ := if b then 3 else -2
example (P : ℝ → Prop) (b : Bool) (h : P (if b = true then 3 else -2)) : P (w b) := by
  simp only [w]
  exact h

/-! ### R4. `simp` on `if b = true then x else y` with `b` a literal · goal: picks the branch
`if b then …` with `b : Bool` is printed `if b = true then …`. -/
example (x y : ℝ) (P : ℝ → Prop) (h₁ : P x) (h₂ : P y) :
    P (if true = true then x else y) ∧ P (if false = true then x else y) := by
  simp
  exact ⟨h₁, h₂⟩

/-! ### R5. `simp` on `∑ _i : Fin n, c` · goal: a sum of a constant → `↑n * c`
Lemmas used: `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul`. -/
example (n : ℕ) (c : ℝ) (P : ℝ → Prop) (h : P (↑n * c)) : P (∑ _i : Fin n, c) := by
  simp
  exact h

/-! ## Lower bounds -/

/-! ### R6. `rintro _ ⟨x, rfl⟩` on `a ∈ lowerBounds (Set.range f)` · context gains `x`; goal → `a ≤ f x`
`a ∈ lowerBounds s` means `∀ ⦃y⦄, y ∈ s → a ≤ y`. `rintro` introduces `y` and `y ∈ Set.range f`,
splits the `∃` into `x`, and `rfl` replaces `y` by `f x` everywhere. -/
example {α β : Type} [Preorder β] (f : α → β) (a : β) (h : ∀ x, a ≤ f x) :
    a ∈ lowerBounds (Set.range f) := by
  rintro _ ⟨x, rfl⟩
  exact h x

/-! ### R7. `cases b` with `b : Bool` · context loses `b`; goal → one goal per value -/
example (P : Bool → Prop) (hf : P false) (ht : P true) (b : Bool) : P b := by
  cases b
  exacts [hf, ht]

/-! ### R8. `norm_num [D]` · closes a numeric goal after unfolding `D` (R3 + R4 + arithmetic) -/
example : w true * w false ≤ 1 := by norm_num [w]

/-! ## Bounding a sum -/

/-! ### R9. `calc` · goal `a ≤ c` → one proof per step `a ≤ b`, `b = c` -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := by
  calc a ≤ b := h₁
    _ = c := h₂

/-! ### R10. `Finset.sum_le_sum` · `(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`
`∑ i : Fin n, f i` is `∑ i ∈ Finset.univ, f i`. As a term: `Finset.sum_le_sum fun i _ => h i`. -/
example (n : ℕ) (f g : Fin n → ℝ) (h : ∀ i, f i ≤ g i) : ∑ i, f i ≤ ∑ i, g i := by
  apply Finset.sum_le_sum
  intro i _
  exact h i

/-! ## Finishing -/

/-! ### R11. `unfold D` · goal: the name `D` → its body (also for a `D` applied to arguments) -/
def lin (k x : ℝ) : ℝ := -k * x
example (k x : ℝ) (P : ℝ → Prop) (h : P (-k * x)) : P (lin k x) := by
  unfold lin
  exact h

/-! ### R12. `nlinarith` · closes a (non)linear inequality from hypotheses, multiplying pairs of them
Here it multiplies `0 ≤ k` by `0 ≤ m - S` (from `S ≤ m`). -/
example (k S m : ℝ) (hk : 0 ≤ k) (h : S ≤ m) : -k * m ≤ -k * S := by nlinarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A least element of a range over `Bool`: R1, R2, R4, R6, R7 -/
example : IsLeast (Set.range w) (-2) := by
  refine ⟨⟨false, by simp [w]⟩, ?_⟩
  rintro _ ⟨b, rfl⟩
  cases b <;> norm_num [w]

/-! ### W2. A sum of bounded terms is bounded: R9, R10, R5 -/
example (n : ℕ) (f : Fin n → ℝ) (hf : ∀ i, f i ≤ 3) : ∑ i, f i ≤ n * 3 := by
  calc ∑ i, f i ≤ ∑ _i : Fin n, (3 : ℝ) := Finset.sum_le_sum fun i _ => hf i
    _ = n * 3 := by simp

/-! ### W3. Scaling a bound by a nonpositive factor: R11, R12 -/
example (k x m : ℝ) (hk : 0 ≤ k) (hx : x ≤ m) : lin k m ≤ lin k x := by
  unfold lin
  nlinarith

end M164Guide

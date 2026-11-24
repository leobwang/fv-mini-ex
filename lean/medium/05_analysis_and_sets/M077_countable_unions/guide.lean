/- Guide for M077 (Countable unions of countable sets).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other sequences, other sets).
Assumed: Lean basics.
-/
import Mathlib

namespace M077Guide

/-! # Part R · Reference entries -/

/-! ## Giving a sequence, taking a point -/

/-! ### R1. `refine ⟨f, ?_⟩` on `∃ g, s ⊆ Set.range g` · goal: the witness `f` is filled in
`refine` unfolds a `def` whose body is an `∃` (W1), so the same move works on such a definition. -/
example {α : Type} (s : Set α) (f : ℕ → α) (h : s ⊆ Set.range f) :
    ∃ g : ℕ → α, s ⊆ Set.range g := by
  refine ⟨f, ?_⟩
  exact h

/-! ### R2. `intro x hx` on `s ⊆ t` · goal `s ⊆ t` → context gains `x`, `hx : x ∈ s`; goal `x ∈ t`
`s ⊆ t` is by definition `∀ x, x ∈ s → x ∈ t`. -/
example {α : Type} (s t : Set α) (h : ∀ x, x ∈ s → x ∈ t) : s ⊆ t := by
  intro x hx
  exact h x hx

/-! ### R3. `refine ⟨y, ?_⟩` on `x ∈ Set.range f` · goal → `f y = x`
`Set.mem_range : x ∈ Set.range f ↔ ∃ y, f y = x` holds by definition, so the anonymous
constructor builds the membership directly. -/
example {α : Type} (f : ℕ → α) (x : α) (y : ℕ) (h : f y = x) : x ∈ Set.range f := by
  refine ⟨y, ?_⟩
  exact h

/-! ### R4. `Nat.unpair_pair` · `Nat.unpair (Nat.pair a b) = (a, b)` · goal: decode of a code
`Nat.pair : ℕ → ℕ → ℕ` codes a pair as one number; `Nat.unpair : ℕ → ℕ × ℕ` decodes it. -/
example (a b : ℕ) (P : ℕ × ℕ → Prop) (h : P (a, b)) : P (Nat.unpair (Nat.pair a b)) := by
  rw [Nat.unpair_pair]
  exact h

/-! ### R5. `simp only [d]` on a sequence `d := fun k => …` · goal: `d k` → the body at `k`
`k.unpair.1` and `k.unpair.2` (printed `(Nat.unpair k).1`, `(Nat.unpair k).2`) are the two
coordinates of the pair that `k` codes. -/
def sumCoords : ℕ → ℕ := fun k => k.unpair.1 + k.unpair.2

example (k : ℕ) (P : ℕ → Prop) (h : P ((Nat.unpair k).1 + (Nat.unpair k).2)) :
    P (sumCoords k) := by
  simp only [sumCoords]
  exact h

/-! ## Using membership facts -/

/-! ### R6. `obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx` · context: `hx : x ∈ ⋃ i, s i` gives `i`, `hi : x ∈ s i`
`Set.mem_iUnion : x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i`; `.mp` is its left-to-right direction. -/
example {α : Type} (s : ℕ → Set α) (x : α) (hx : x ∈ ⋃ i, s i) (P : Prop)
    (h : ∀ i, x ∈ s i → P) : P := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact h i hi

/-! ### R7. `have hxt := hst hx` · context gains `hxt : x ∈ t` from `hst : s ⊆ t`, `hx : x ∈ s`
A subset hypothesis is a function: applied to a membership proof it gives the other membership. -/
example {α : Type} (s t : Set α) (x : α) (hst : s ⊆ t) (hx : x ∈ s) : x ∈ t := by
  have hxt := hst hx
  exact hxt

/-! ### R8. `obtain ⟨m, rfl⟩ := hr` on `hr : x ∈ Set.range f` · context loses `x`, `hr`; `x` → `f m` everywhere -/
example {α : Type} (f : ℕ → α) (x : α) (hr : x ∈ Set.range f) (P : α → Prop)
    (h : ∀ m, P (f m)) : P x := by
  obtain ⟨m, rfl⟩ := hr
  exact h m

/-! ## Choosing one witness per index -/

/-! ### R9. `choose F hF using h` · context: `h : ∀ n, ∃ g, Q n g` → `F : ℕ → (ℕ → α)`, `hF : ∀ n, Q n (F n)`
`choose` also unfolds a `def` whose body is an `∃`. -/
example {α : Type} (Q : ℕ → (ℕ → α) → Prop) (h : ∀ n : ℕ, ∃ g : ℕ → α, Q n g) (R : Prop)
    (k : ∀ F : ℕ → ℕ → α, (∀ n, Q n (F n)) → R) : R := by
  choose F hF using h
  exact k F hF

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `refine` sees through a `def` whose body is an `∃` (R1) -/
def Hits (s : Set ℕ) : Prop := ∃ n, n ∈ s

example : Hits {3} := by
  refine ⟨3, ?_⟩
  rfl

/-! ### W2. Every `n : ℕ` is hit by the first coordinate: R2, R3, R4 -/
example : Set.univ ⊆ Set.range (fun k : ℕ => k.unpair.1) := by
  intro n _
  refine ⟨Nat.pair n 0, ?_⟩
  simp [Nat.unpair_pair]

/-! ### W3. Unfold a sequence, then decode: R5, R4 (`rw` closes the goal by `rfl`) -/
example (a b : ℕ) : sumCoords (Nat.pair a b) = a + b := by
  simp only [sumCoords]
  rw [Nat.unpair_pair]

/-! ### W4. Range of `f` inside the range of a reindexed sequence: R2, R8, R3, R4 -/
example {α : Type} (f : ℕ → α) : Set.range f ⊆ Set.range (fun k : ℕ => f k.unpair.2) := by
  intro x hx
  obtain ⟨m, rfl⟩ := hx
  refine ⟨Nat.pair 0 m, ?_⟩
  simp [Nat.unpair_pair]

/-! ### W5. One sequence covering every piece covers the union: R2, R6, R7 -/
example {α : Type} (s : ℕ → Set α) (f : ℕ → α) (hs : ∀ i, s i ⊆ Set.range f) :
    ⋃ i, s i ⊆ Set.range f := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact hs i hi

/-! ### W6. `choose`, then package the chosen function: R9, R1 -/
example (h : ∀ n : ℕ, ∃ m : ℕ, n < m) : ∃ g : ℕ → ℕ, ∀ n, n < g n := by
  choose g hg using h
  exact ⟨g, hg⟩

end M077Guide

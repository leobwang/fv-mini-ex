/- Guide for M074 (Computing a supremum).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g`) in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a constant sequence, `[0, 1)`).
Assumed: Lean basics.
-/
import Mathlib

namespace M074Guide

/-! # Part R · Reference entries -/

/-! ## From `sSup s = a` to "least upper bound" -/

/-! ### R1. `apply IsLUB.csSup_eq` · goal `sSup s = a` → two goals: `IsLUB s a`, `s.Nonempty`
`IsLUB.csSup_eq : IsLUB s a → s.Nonempty → sSup s = a` in a conditionally complete lattice (ℝ is one). -/
example {α : Type} [ConditionallyCompleteLattice α] (s : Set α) (a : α) (h : IsLUB s a)
    (hne : s.Nonempty) : sSup s = a := by
  apply IsLUB.csSup_eq
  exact h
  exact hne

/-! ### R2. `refine ⟨f i, ?_⟩`, then `Set.mem_range_self i` · `(Set.range f).Nonempty` is `∃ x, x ∈ Set.range f`
`Set.mem_range_self i : f i ∈ Set.range f`. As one term: `⟨_, Set.mem_range_self i⟩`. -/
example {ι α : Type} (f : ι → α) (i : ι) : (Set.range f).Nonempty := by
  refine ⟨f i, ?_⟩
  exact Set.mem_range_self i

/-! ### R3. `constructor` on `IsLUB s a` · goal → two goals: upper bound, and least among upper bounds
`IsLUB s a` unfolds to `a ∈ upperBounds s ∧ a ∈ lowerBounds (upperBounds s)`. -/
example {α : Type} [Preorder α] (s : Set α) (a : α) (h1 : a ∈ upperBounds s)
    (h2 : a ∈ lowerBounds (upperBounds s)) : IsLUB s a := by
  constructor
  exact h1
  exact h2

/-! ## Part 1 of `IsLUB`: an upper bound -/

/-! ### R4. `rintro _ ⟨n, rfl⟩` · goal `a ∈ upperBounds (Set.range f)` → context gains `n`, goal `f n ≤ a`
`a ∈ upperBounds s` means `∀ ⦃x⦄, x ∈ s → x ≤ a`; `x ∈ Set.range f` means `∃ n, f n = x`.
The pattern takes `x`, splits the `∃`, and `rfl` replaces `x` by `f n` everywhere. -/
example {ι : Type} (f : ι → ℝ) (a : ℝ) (h : ∀ n, f n ≤ a) : a ∈ upperBounds (Set.range f) := by
  rintro _ ⟨n, rfl⟩
  exact h n

/-! ### R5. `positivity` · closes a goal `0 < e` or `0 ≤ e` when `e` is built from positive pieces -/
example (n : ℕ) (c : ℝ) (hc : 0 < c) : 0 < c / ((n : ℝ) + 2) := by
  positivity

/-! ### R6. `dsimp only` · goal: `(fun k => body) n` → `body` with `n` substituted (beta reduction) -/
example (g : ℕ → ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (g n + 1)) : P ((fun k => g k + 1) n) := by
  dsimp only
  exact h

/-! ### R7. `linarith` · closes a linear (in)equality, or `False`, from the hypotheses in context
It treats every non-linear piece such as `1 / (↑n + 1)` as an unknown. -/
example (x y : ℝ) (hx : 0 < x) : y - x ≤ y := by
  linarith

example (x y : ℝ) (h1 : x ≤ y) (h2 : y < x) : False := by
  linarith

/-! ## Part 2 of `IsLUB`: least among upper bounds -/

/-! ### R8. `intro b hb` · goal `a ∈ lowerBounds (upperBounds s)` → context gains `b`, `hb`, goal `a ≤ b`
`a ∈ lowerBounds t` means `∀ ⦃b⦄, b ∈ t → a ≤ b`. -/
example {α : Type} [Preorder α] (s : Set α) (a : α) (h : ∀ b ∈ upperBounds s, a ≤ b) :
    a ∈ lowerBounds (upperBounds s) := by
  intro b hb
  exact h b hb

/-! ### R9. `by_contra hlt` · goal `G` → context gains `hlt : ¬G`, goal `False` -/
example (a b : ℝ) (h : ¬a ≤ b → False) : a ≤ b := by
  by_contra hlt
  exact h hlt

/-! ### R10. `push Not at hlt` · context: `hlt : ¬a ≤ b` → `hlt : b < a` (the negation pushed inward) -/
example (a b : ℝ) (hlt : ¬a ≤ b) (g : b < a → False) : False := by
  push Not at hlt
  exact g hlt

/-! ### R11. `obtain ⟨n, hn⟩ := exists_nat_gt x` · context gains `n : ℕ`, `hn : x < ↑n`
`exists_nat_gt x : ∃ n : ℕ, x < ↑n` is the Archimedean property: no real is above every natural. -/
example (x : ℝ) (G : Prop) (g : ∀ n : ℕ, x < n → G) : G := by
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact g n hn

/-! ### R12. `have hbn : f n ≤ b := hb ⟨n, rfl⟩` · context gains the bound for one element of the range
`hb : b ∈ upperBounds (Set.range f)` is a function: give it a proof of `f n ∈ Set.range f`
(`⟨n, rfl⟩`, or `Set.mem_range_self n`) and it returns `f n ≤ b`. -/
example {ι : Type} (f : ι → ℝ) (b : ℝ) (hb : b ∈ upperBounds (Set.range f)) (n : ι) (G : Prop)
    (g : f n ≤ b → G) : G := by
  have hbn : f n ≤ b := hb ⟨n, rfl⟩
  exact g hbn

/-! ### R13. `rw [div_lt_iff₀ hc]` · goal `a / c < b` → `a < b * c`
`div_lt_iff₀ (hc : 0 < c) : a / c < b ↔ a < b * c`. Write `div_lt_iff₀ (by positivity)` for the `0 < c`. -/
example (a b c : ℝ) (hc : 0 < c) (h : a < b * c) : a / c < b := by
  rw [div_lt_iff₀ hc]
  exact h

/-! ### R14. `rw [div_lt_iff₀ hc] at hn` · context: `hn : a / c < b` → `hn : a < b * c` -/
example (a b c : ℝ) (hc : 0 < c) (hn : a / c < b) (g : a < b * c → False) : False := by
  rw [div_lt_iff₀ hc] at hn
  exact g hn

/-! ### R15. `nlinarith` · closes an (in)equality that needs hypotheses multiplied together
Like `linarith`, but it also adds products of pairs of hypotheses. Here it multiplies `0 < x` by
`0 < y - 1`; `linarith` alone fails on this example. -/
example (x y : ℝ) (hx : 0 < x) (h : 1 < y) : x < x * y := by
  nlinarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R1 with R2 passed inline, then R3, R4, R6, R8, R12: a constant sequence -/
example : sSup (Set.range fun _ : ℕ => (2 : ℝ)) = 2 := by
  apply IsLUB.csSup_eq _ ⟨_, Set.mem_range_self 0⟩
  constructor
  · rintro _ ⟨n, rfl⟩
    dsimp only
    rfl
  · intro b hb
    exact hb ⟨0, rfl⟩

/-! ### W2. Least upper bound by contradiction (R3, R8, R9, R10, R7) for `[0, 1)`
`x ∈ Set.Ico a b` means `a ≤ x ∧ x < b`. Against `b < 1`, the witness is the midpoint `(b + 1) / 2`. -/
example : IsLUB (Set.Ico (0 : ℝ) 1) 1 := by
  constructor
  · intro x hx
    exact hx.2.le
  · intro b hb
    by_contra hlt
    push Not at hlt
    have h0 : 0 ≤ b := hb ⟨le_refl 0, one_pos⟩
    have hm : (b + 1) / 2 ≤ b := hb ⟨by linarith, by linarith⟩
    linarith

/-! ### W3. The Archimedean step: from `0 < c` get `n` with `1 < n * c` (R11, R14) -/
example (c : ℝ) (hc : 0 < c) : ∃ n : ℕ, 1 < (n : ℝ) * c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / c)
  rw [div_lt_iff₀ hc] at hn
  exact ⟨n, hn⟩

end M074Guide

/- Guide for H046 (Heine–Borel for [0, 1]).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`, or `P` is
the whole goal. A hypothesis `h`/`k` in an entry is only there to finish the example; it shows what
the goal or the context became.
Part W: worked combinations on objects that are NOT the exercise's (a two-element finset, a concrete
ball, the set `[0, 2]`, a `min` with `5`).
Assumed: Lean basics (E001–E033). New: Mathlib's sets (`{x | p x}`, `Icc`, `⊆`, `⋃`), `Finset`
(`{i}`, `insert`), metric balls and `dist`, `|·|`, `IsOpen`, `sSup`/`BddAbove`/`Nonempty`, `min`,
and the tactics `classical`, `by_cases`, `push Not`, `set`, `linarith`.
-/
import Mathlib

open Set

namespace H046Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · `zero_mem_S`: `[0, 0]` is finitely covered -/

/-! ### R1. `classical` · context: every proposition becomes decidable; the goal is unchanged
`insert j t` on a `Finset ι` must decide `j = i` for each element `i` of `t`, so it needs
`DecidableEq ι`. After `classical` that instance exists (it is not printed in the context). -/
example {ι : Type} (j : ι) (t : Finset ι) (P : Finset ι → Prop) (k : ∀ u, P u) :
    ∃ u, P u := by
  classical
  exact ⟨insert j t, k _⟩

/-! ### R2. `Set.mem_setOf_eq` · `(a ∈ {x | p x}) = p a` · goal: membership → the property -/
example {α : Type} (p : α → Prop) (a : α) (h : p a) : a ∈ {x | p x} := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ### R3. `Set.mem_Icc` · `x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b` · goal: membership → two inequalities
Both R2 and R3 hold by definition, so `⟨ha, hb⟩` proves `x ∈ Icc a b` and `hx.1`, `hx.2` take
`hx : x ∈ Icc a b` apart without any `rw`. -/
example (a b x : ℝ) (h : a ≤ x ∧ x ≤ b) : x ∈ Icc a b := by
  rw [Set.mem_Icc]
  exact h

example (a b x : ℝ) (hx : x ∈ Icc a b) (P : Prop) (k : x ≤ b → P) : P := by
  have h2 : x ≤ b := hx.2
  exact k h2

/-! ### R4. `le_rfl` · `a ≤ a` · closes the goal -/
example {α : Type} [Preorder α] (a : α) : a ≤ a := le_rfl

/-! ### R5. `zero_le_one` · `0 ≤ 1` · closes the goal (in `ℝ`, `ℕ`, any ordered semiring) -/
example : (0 : ℝ) ≤ 1 := zero_le_one

/-! ### R6. `refine ⟨⟨ha, hb⟩, ?_⟩` · goal `x ∈ {y | y ∈ Icc a b ∧ Q y}` → `Q x`
R2 and R3 by definition: the outer pair is the `∧`, the inner pair is the `Icc` membership. -/
example (a b x : ℝ) (Q : ℝ → Prop) (ha : a ≤ x) (hb : x ≤ b) (hq : Q x) :
    x ∈ {y | y ∈ Icc a b ∧ Q y} := by
  refine ⟨⟨ha, hb⟩, ?_⟩
  exact hq

/-! ### R7. `h hx` · a subset applied to a membership · context gains `x ∈ B`
`A ⊆ B` unfolds to `∀ ⦃z⦄, z ∈ A → z ∈ B`, so `h : A ⊆ B` is a function on proofs of membership. -/
example {α : Type} (A B : Set α) (h : A ⊆ B) (x : α) (hx : x ∈ A) (P : Prop) (k : x ∈ B → P) : P := by
  have hB := h hx
  exact k hB

/-! ### R8. `Set.mem_iUnion` · `x ∈ ⋃ i, U i ↔ ∃ i, x ∈ U i` · context: pick the index -/
example {ι : Type} (U : ι → Set ℝ) (x : ℝ) (h : x ∈ ⋃ i, U i) (P : Prop)
    (k : ∀ i, x ∈ U i → P) : P := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
  exact k i hi

/-! ### R9. `intro z hz` on `A ⊆ B` · goal → context gains `z`, `hz : z ∈ A`; goal `z ∈ B`
Inside a term, `fun z hz => ?_` does the same: `refine ⟨t, fun z hz => ?_⟩`. -/
example {α : Type} (A B : Set α) (k : ∀ z, z ∈ A → z ∈ B) : A ⊆ B := by
  intro z hz
  exact k z hz

/-! ### R10. `le_antisymm` · `a ≤ b → b ≤ a → a = b` · context gains the equation -/
example (a b : ℝ) (h1 : a ≤ b) (h2 : b ≤ a) (P : Prop) (k : a = b → P) : P := by
  have h := le_antisymm h1 h2
  exact k h

/-! ### R11. `Set.mem_iUnion₂` · `x ∈ ⋃ i, ⋃ j, s i j ↔ ∃ i j, x ∈ s i j`
`⋃ i ∈ t, U i` is `⋃ i, ⋃ (_ : i ∈ t), U i`, so here the `j` is a proof of `i ∈ t`.
`.mpr ⟨i, hi, hx⟩` proves a membership (goal); `.mp h` takes one apart (context). -/
example {ι : Type} (U : ι → Set ℝ) (t : Finset ι) (x : ℝ) (i : ι) (hi : i ∈ t) (hx : x ∈ U i) :
    x ∈ ⋃ i ∈ t, U i := by
  rw [Set.mem_iUnion₂]
  exact ⟨i, hi, hx⟩

example {ι : Type} (U : ι → Set ℝ) (t : Finset ι) (x : ℝ) (h : x ∈ ⋃ i ∈ t, U i) (P : Prop)
    (k : ∀ i ∈ t, x ∈ U i → P) : P := by
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
  exact k i hi hxi

/-! ### R12. `Finset.mem_singleton_self` · `a ∈ ({a} : Finset α)` · closes the goal -/
example {ι : Type} (i : ι) : i ∈ ({i} : Finset ι) := Finset.mem_singleton_self i

/-! ### R13. `h ▸ e` · from `h : a = b` and `e` proving the goal with one side replaced · closes it
`▸` rewrites with `h` (trying both directions) until the type of `e` fits the goal. -/
example {α : Type} (P : α → Prop) (a b : α) (h : a = b) (e : P b) : P a := by
  exact h ▸ e

/-! ## Part 2 · `extend_cover`: adding one open set pushes the cover to the right -/

/-! ### R14. `by_cases h : p` · goal list: one goal with `h : p`, one with `h : ¬p` -/
example (p Q : Prop) (k1 : p → Q) (k2 : ¬p → Q) : Q := by
  by_cases h : p
  · exact k1 h
  · exact k2 h

/-! ### R15. `Finset.mem_insert_of_mem` · `a ∈ s → a ∈ insert b s` · context or goal
`insert b s` is the finset `s` with `b` added (`{b} ∪ s`); it needs `DecidableEq` (R1). -/
example {ι : Type} [DecidableEq ι] (i j : ι) (t : Finset ι) (hi : i ∈ t) (P : Prop)
    (k : i ∈ insert j t → P) : P := by
  have h : i ∈ insert j t := Finset.mem_insert_of_mem hi
  exact k h

/-! ### R16. `push Not at h` · context: `¬(a ≤ b)` → `b < a` (pushes `¬` inward) -/
example (a b : ℝ) (P : Prop) (k : b < a → P) (h : ¬a ≤ b) : P := by
  push Not at h
  exact k h

/-! ### R17. `Finset.mem_insert_self` · `a ∈ insert a s` · closes the goal -/
example {ι : Type} [DecidableEq ι] (j : ι) (t : Finset ι) : j ∈ insert j t :=
  Finset.mem_insert_self j t

/-! ### R18. `Metric.mem_ball` · `y ∈ Metric.ball x ε ↔ dist y x < ε` · goal -/
example (x y ε : ℝ) (P : Prop → Prop) (h : P (dist y x < ε)) : P (y ∈ Metric.ball x ε) := by
  rw [Metric.mem_ball]
  exact h

/-! ### R19. `Real.dist_eq` · `dist x y = |x - y|` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P |y - x|) : P (dist y x) := by
  rw [Real.dist_eq]
  exact h

/-! ### R20. `abs_lt` · `|a| < b ↔ -b < a ∧ a < b` · goal -/
example (a b : ℝ) (h : -b < a ∧ a < b) : |a| < b := by
  rw [abs_lt]
  exact h

/-! ### R21. `min_le_left` · `min a b ≤ a` · a term to feed `le_trans` or `linarith` -/
example (a b : ℝ) : min a b ≤ a := min_le_left a b

/-! ### R22. `min_le_right` · `min a b ≤ b` -/
example (a b : ℝ) : min a b ≤ b := min_le_right a b

/-! ### R23. `le_trans`, written `h1.trans h2` · `a ≤ b → b ≤ c → a ≤ c` · context -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (P : Prop) (k : a ≤ c → P) : P := by
  have h := h1.trans h2
  exact k h

/-! ### R24. `linarith [t₁, t₂]` · closes a linear (in)equality from the context plus the terms `tᵢ`
It treats `min a b`, `|a|`, `sSup S` as unknowns; facts about them must be supplied. Here plain
`linarith` fails: it does not know `min a b ≤ a` until the term `min_le_left a b` is passed. -/
example (a b c : ℝ) (h : c ≤ min a b) : c ≤ a + 1 := by
  linarith [min_le_left a b]

/-! ## Part 3 · `heine_borel`: the supremum argument -/

/-! ### R25. `set S : Set ℝ := e` · context gains the local definition `S : Set ℝ := e`;
every `e` in the goal is replaced by `S` -/
example (a b : ℝ) (P : Set ℝ → Prop) (k : ∀ S : Set ℝ, P S) : P (Icc a b) := by
  set S : Set ℝ := Icc a b
  exact k S

/-! ### R26. `refine ⟨b, fun x hx => ?_⟩` on `BddAbove S` · goal → `x ≤ b`, context `x`, `hx : x ∈ S`
`BddAbove S` unfolds to `∃ b, b ∈ upperBounds S`, and `b ∈ upperBounds S` to `∀ ⦃x⦄, x ∈ S → x ≤ b`. -/
example (S : Set ℝ) (b : ℝ) (k : ∀ x ∈ S, x ≤ b) : BddAbove S := by
  refine ⟨b, fun x hx => ?_⟩
  exact k x hx

/-! ### R27. `le_csSup` · `BddAbove S → a ∈ S → a ≤ sSup S` · context -/
example (S : Set ℝ) (hb : BddAbove S) (a : ℝ) (ha : a ∈ S) (P : Prop) (k : a ≤ sSup S → P) : P := by
  have h := le_csSup hb ha
  exact k h

/-! ### R28. `csSup_le` · `S.Nonempty → (∀ b ∈ S, b ≤ a) → sSup S ≤ a` · context
`S.Nonempty` unfolds to `∃ x, x ∈ S`: give it as `⟨x, hx⟩`. -/
example (S : Set ℝ) (x a : ℝ) (hx : x ∈ S) (hS : ∀ b ∈ S, b ≤ a) (P : Prop)
    (k : sSup S ≤ a → P) : P := by
  have h := csSup_le ⟨x, hx⟩ hS
  exact k h

/-! ### R29. `Metric.isOpen_iff` · `IsOpen V ↔ ∀ x ∈ V, ∃ ε > 0, Metric.ball x ε ⊆ V` · context -/
example (V : Set ℝ) (hV : IsOpen V) (c : ℝ) (hc : c ∈ V) (P : Prop)
    (k : ∀ ε > 0, Metric.ball c ε ⊆ V → P) : P := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV c hc
  exact k ε hε hball

/-! ### R30. `exists_lt_of_lt_csSup` · `S.Nonempty → b < sSup S → ∃ a ∈ S, b < a` · context -/
example (S : Set ℝ) (hne : S.Nonempty) (b : ℝ) (hb : b < sSup S) (P : Prop)
    (k : ∀ a ∈ S, b < a → P) : P := by
  obtain ⟨a, ha, hba⟩ := exists_lt_of_lt_csSup hne hb
  exact k a ha hba

/-! ### R31. `sub_lt_self` · `0 < b → a - b < a` · context -/
example (a b : ℝ) (hb : 0 < b) (P : Prop) (k : a - b < a → P) : P := by
  have h := sub_lt_self a hb
  exact k h

/-! ### R32. `obtain ⟨x, -, hB⟩ := h` · context: the `-` pattern drops a component you do not need -/
example (A B : ℝ → Prop) (P : Prop) (k : ∀ x, B x → P) (h : ∃ x, A x ∧ B x) : P := by
  obtain ⟨x, -, hB⟩ := h
  exact k x hB

/-! ### R33. `le_min` · `a ≤ b → a ≤ c → a ≤ min b c` · closes the goal given both halves -/
example (a b c : ℝ) (hb : a ≤ b) (hc : a ≤ c) : a ≤ min b c := by
  exact le_min hb hc

/-! ### R34. `rcases min_choice a b with h | h` · goal list: `h : min a b = a` / `h : min a b = b` -/
example (a b : ℝ) (P : ℝ → Prop) (h1 : P a) (h2 : P b) : P (min a b) := by
  rcases min_choice a b with h | h
  · rw [h]
    exact h1
  · rw [h]
    exact h2

/-! ### R35. `have h' : y = e := h` · context: restate `h` through a `set` name
After `set y := min a b`, a hypothesis made later (by `rcases min_choice a b`, say) still says
`min a b`. The restatement is accepted with no proof work because `y` is by definition `min a b`;
it puts the fact in the same words as the rest of the context.
(`min_eq_left : a ≤ b → min a b = a` only supplies a hypothesis of that shape here.) -/
example (a b : ℝ) (hab : a ≤ b) (P : ℝ → Prop) (k : ∀ y : ℝ, y = a → P y) : P (min a b) := by
  set y := min a b
  have h : min a b = a := min_eq_left hab
  have h' : y = a := h
  exact k y h'

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A point of `V j` lies in the union over the finset `{i, j}`: R11, R15, R12
`{i, j}` is `insert i {j}`. -/
example {ι : Type} [DecidableEq ι] (V : ι → Set ℝ) (i j : ι) (x : ℝ) (hx : x ∈ V j) :
    x ∈ ⋃ k ∈ ({i, j} : Finset ι), V k := by
  rw [Set.mem_iUnion₂]
  exact ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j), hx⟩

/-! ### W2. Membership in a concrete ball: R18, R19, R20, then two numeric goals -/
example : (5 / 4 : ℝ) ∈ Metric.ball 1 (1 / 2) := by
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> norm_num

/-! ### W3. `sSup` of `[0, 2]` written as a set-builder set lies in `[0, 2]`: R25, R26, R27, R28 -/
example : sSup {x : ℝ | 0 ≤ x ∧ x ≤ 2} ∈ Icc 0 2 := by
  set T : Set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 2}
  have h0 : (0 : ℝ) ∈ T := ⟨le_rfl, by norm_num⟩
  have hbdd : BddAbove T := ⟨2, fun x hx => hx.2⟩
  exact ⟨le_csSup hbdd h0, csSup_le ⟨0, h0⟩ fun x hx => hx.2⟩

/-! ### W4. A `min` that is at most `a` must be its other argument: R25, R34, R35, R24
In the first case `m = a + 1` and `m ≤ a` contradict each other, so `linarith` closes any goal. -/
example (a : ℝ) (hle : min (a + 1) 5 ≤ a) : min (a + 1) 5 = 5 := by
  set m := min (a + 1) 5
  rcases min_choice (a + 1) 5 with h | h
  · have h' : m = a + 1 := h
    linarith
  · exact h

end H046Guide

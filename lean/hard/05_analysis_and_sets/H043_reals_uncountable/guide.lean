/- Guide for H043 (ℝ is uncountable).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about definitions use the guide's own `order` (sort a pair), `T` (a recursive sequence
of pairs) and `g`, which are NOT the exercise's `step` and `I`.
Part W: worked combinations on `order`, a halving sequence `J`, and a bounded sequence.
Assumed: Lean basics (E001–E033). New: Mathlib's `ℝ` with its order, pairs `ℝ × ℝ`, `if` in a
definition, `split_ifs`, `push Not`, `linarith`, `Monotone`/`Antitone`, `max`, `Set.range`,
`BddAbove`, `sSup`.
The import lines are the exercise's frozen imports; its BANNED line forbids adding more.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace H043Guide

/-! # Part R · Reference entries -/

/-! ## Writing a pair-valued definition with `if` -/

/-! ### R1. `if c then (a, b) else (a', b')` · a definition body that branches on a real comparison
`(a, b) : ℝ × ℝ` is a pair; `p.1`, `p.2` are its components. `x < y` on `ℝ` is not computable, so a
definition that tests it must be marked `noncomputable` (the exercise's `step` already is). -/
noncomputable def order (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.1 ≤ p.2 then p else (p.2, p.1)

example : (order (3, 1)).1 = 1 := by norm_num [order]

/-! ## Proving facts about such a definition -/

/-! ### R2. `unfold order` · goal: the name → its body -/
example (p : ℝ × ℝ) (P : ℝ × ℝ → Prop) (h : P (if p.1 ≤ p.2 then p else (p.2, p.1))) :
    P (order p) := by
  unfold order
  exact h

/-! ### R3. `split_ifs with hc` · goal list: one goal per branch; context gains `hc : c` / `hc : ¬c` -/
example (c : Prop) [Decidable c] (a b : ℝ) (P : ℝ → Prop) (ha : c → P a) (hb : ¬c → P b) :
    P (if c then a else b) := by
  split_ifs with hc
  exact ha hc
  exact hb hc

/-! ### R4. `simp only` (no lemmas) · goal: `(a, b).1` → `a`, `(a, b).2` → `b` -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P a b) : P (a, b).1 (a, b).2 := by
  simp only
  exact h

/-! ### R5. `linarith` · closes a goal `t < s`, `t ≤ s`, `t = s` or `False` that follows linearly
from the hypotheses. Anything that is not `+`, `-`, a numeral or a numeral times a term (such as
`p.1` or `f n`) is an unknown. -/
example (a b z : ℝ) (h : a < b) (hz : z < a) : z < (a + 2 * b) / 3 := by
  linarith

/-! ### R6. `le_rfl` · `a ≤ a` · closes the goal -/
example {α : Type} [Preorder α] (a : α) : a ≤ a := le_rfl

/-! ### R7. `push Not at hc` · context: `hc : ¬a < b` → `hc : b ≤ a` -/
example (a b : ℝ) (P : Prop) (hc : ¬a < b) (h : b ≤ a → P) : P := by
  push Not at hc
  exact h hc

/-! ## Recursive sequences -/

/-- A toy recursive sequence of pairs. -/
noncomputable def T : ℕ → ℝ × ℝ
  | 0 => (0, 2)
  | n + 1 => ((T n).1, (T n).2 / 2)

/-! ### R8. `simp [T]` · at index `0`: unfolds `T 0`, reduces the pair, decides the numbers · closes -/
example : (T 0).1 < (T 0).2 := by
  simp [T]

/-! ### R9. `simp only [T] at h` · context: `T (n + 1)` in `h` → one unfolding step
Without `at h` it acts on the goal. `exact` sees through one step without it (`T (n + 1)` *is*
`((T n).1, (T n).2 / 2)` by definition). -/
example (n : ℕ) (P : ℝ → Prop) (h : P (T (n + 1)).2) (h' : P ((T n).2 / 2) → False) : False := by
  simp only [T] at h
  exact h' h

/-! ### R10. `h.1`, `h.2.1`, `h.2.2.1`, `h.2.2.2` · the parts of `h : A ∧ B ∧ C ∧ D` · context
`∧` nests to the right, so `.2` is "the rest" and `.2.2.1` is the third part. -/
example (A B C D : Prop) (h : A ∧ B ∧ C ∧ D) (P : Prop) (hp : C → P) : P := by
  have hc := h.2.2.1
  exact hp hc

/-! ## Monotone sequences -/

/-! ### R11. `hm hab` with `hm : Monotone g`, `hab : a ≤ b` · context gains `g a ≤ g b`
`Monotone g` is `∀ ⦃a b⦄, a ≤ b → g a ≤ g b`; `Antitone g` is `∀ ⦃a b⦄, a ≤ b → g b ≤ g a`. -/
example (g : ℕ → ℝ) (hm : Monotone g) (a b : ℕ) (hab : a ≤ b) (P : Prop) (h : g a ≤ g b → P) :
    P := by
  have hg := hm hab
  exact h hg

/-! ### R12. `monotone_nat_of_le_succ` · `(∀ n, g n ≤ g (n + 1)) → Monotone g` · goal: one step -/
example (g : ℕ → ℝ) (h : ∀ n, g n ≤ g (n + 1)) : Monotone g := by
  apply monotone_nat_of_le_succ
  exact h

/-! ### R13. `antitone_nat_of_succ_le` · `(∀ n, g (n + 1) ≤ g n) → Antitone g` · goal: one step -/
example (g : ℕ → ℝ) (h : ∀ n, g (n + 1) ≤ g n) : Antitone g := by
  apply antitone_nat_of_succ_le
  exact h

/-! ### R14. `le_max_left a b : a ≤ max a b`, `le_max_right a b : b ≤ max a b` · context -/
example (a b : ℕ) (P : Prop) (h : a ≤ max a b → b ≤ max a b → P) : P := by
  have h1 := le_max_left a b
  have h2 := le_max_right a b
  exact h h1 h2

/-! ### R15. `hlt.le` (`LT.lt.le`) · `a < b → a ≤ b` · context -/
example (a b : ℝ) (hlt : a < b) (P : Prop) (h : a ≤ b → P) : P := by
  have hle := hlt.le
  exact h hle

/-! ### R16. `calc` · a chain `a ≤ b`, `_ ≤ c`, `_ ≤ d` proves `a ≤ d` · closes the goal
Each line is `_ ≤ next := proof`; `_` is the previous right-hand side. -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by
  calc a ≤ b := h1
    _ ≤ c := h2
    _ ≤ d := h3

/-! ## Sets of values and least upper bounds -/

/-! ### R17. `set x := e with hx` · context gains `x : ℝ := e` and `hx : x = e`; goal: `e` → `x` -/
example (g : ℕ → ℝ) (P : ℝ → Prop) (h : ∀ y, P y) : P (sSup (Set.range g)) := by
  set x := sSup (Set.range g) with hx
  exact h x

/-! ### R18. `⟨k, rfl⟩ : g k ∈ Set.range g` · membership in the set of values · closes the goal
`Set.range g` is `{y | ∃ k, g k = y}`, so a member is a pair: an index and an equation. -/
example (g : ℕ → ℝ) (k : ℕ) : g k ∈ Set.range g := ⟨k, rfl⟩

/-! ### R19. `refine ⟨M, ?_⟩` on `BddAbove s` · goal → `M ∈ upperBounds s`
`BddAbove s` means `∃ M, M ∈ upperBounds s`, and `M ∈ upperBounds s` means `∀ ⦃y⦄, y ∈ s → y ≤ M`. -/
example (s : Set ℝ) (M : ℝ) (h : M ∈ upperBounds s) : BddAbove s := by
  refine ⟨M, ?_⟩
  exact h

/-! ### R20. `rintro _ ⟨k, rfl⟩` · goal `M ∈ upperBounds (Set.range g)` → `g k ≤ M`, context gains `k`
It introduces the element `y` and its membership `∃ k, g k = y` at once, and `rfl` replaces `y` by
`g k`. The same works on a goal `∀ y ∈ Set.range g, y ≤ M`. -/
example (g : ℕ → ℝ) (M : ℝ) (h : ∀ k, g k ≤ M) : M ∈ upperBounds (Set.range g) := by
  rintro _ ⟨k, rfl⟩
  exact h k

/-! ### R21. `le_csSup` · `BddAbove s → a ∈ s → a ≤ sSup s` · context
`cs` = *conditionally complete*: in `ℝ`, `sSup s` is the least upper bound only when `s` is nonempty
and bounded above, so the lemmas ask for those facts. -/
example (s : Set ℝ) (a : ℝ) (hb : BddAbove s) (ha : a ∈ s) (P : Prop) (h : a ≤ sSup s → P) : P := by
  have hle := le_csSup hb ha
  exact h hle

/-! ### R22. `csSup_le` · `s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a` · goal → two goals -/
example (s : Set ℝ) (a : ℝ) (hne : s.Nonempty) (h : ∀ b ∈ s, b ≤ a) : sSup s ≤ a := by
  apply csSup_le
  exact hne
  exact h

/-! ### R23. `Set.range_nonempty g` · `(Set.range g).Nonempty` for `g : ℕ → α` · context -/
example (g : ℕ → ℝ) (P : Prop) (h : (Set.range g).Nonempty → P) : P := by
  have hne := Set.range_nonempty g
  exact h hne

/-! ### R24. `intro hn` on `a ≠ b` · context gains `hn : a = b`; goal → `False`
`a ≠ b` is `a = b → False`. In a term: `fun hn => …`. -/
example (a b : ℝ) (hab : a < b) : a ≠ b := by
  intro hn
  linarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R2, R3, R4, R5, R7: `order` really sorts the pair -/
example (p : ℝ × ℝ) : (order p).1 ≤ (order p).2 := by
  unfold order
  split_ifs with hc
  · exact hc
  · push Not at hc
    simp only
    linarith

/-- The left half of `[0, 1]`, again and again. -/
noncomputable def J : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | n + 1 => ((J n).1, ((J n).1 + (J n).2) / 2)

/-! ### W2. Induction over a recursive sequence: R8, then R9 on the goal, then R5 -/
example (n : ℕ) : (J n).1 < (J n).2 := by
  induction n with
    | zero => simp [J]
    | succ n ih =>
      simp only [J]
      linarith

/-! ### W3. R12 with R9 and R6: the left endpoints of `J` never decrease -/
example : Monotone (fun n => (J n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [J]
  exact le_rfl

/-! ### W4. R22, R23, R20: every value `≤ 1` puts the least upper bound `≤ 1` -/
example (g : ℕ → ℝ) (hg : ∀ k, g k ≤ 1) : sSup (Set.range g) ≤ 1 := by
  apply csSup_le (Set.range_nonempty g)
  rintro _ ⟨k, rfl⟩
  exact hg k

end H043Guide

/- Guide for H041 (Intermediate value theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`, or `P`
is the whole goal (`P : Prop`). A hypothesis `h` in an entry is only there to finish the example; it
shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a toy set, a toy function `g`).
Assumed: Lean basics (E001–E033). New: Mathlib's least upper bounds on `ℝ` (`sSup`, `BddAbove`,
`Set.Nonempty`, `Set.Icc`), absolute value and `min` on `ℝ`, the tactics `set`, `by_contra`,
`push Not`, `linarith`.
-/
import Mathlib

namespace H041Guide

/-! # Part R · Reference entries -/

/-! ## Least upper bounds: `sSup` and its two side conditions -/

/-! ### R1. `refine ⟨b, ?_⟩` on `BddAbove s` · goal → `b ∈ upperBounds s`
`BddAbove s` unfolds to `∃ b, b ∈ upperBounds s`, and `b ∈ upperBounds s` unfolds to
`∀ ⦃x⦄, x ∈ s → x ≤ b`, so a hypothesis `∀ x ∈ s, x ≤ b` closes it. In one go: `⟨b, h⟩`. -/
example (s : Set ℝ) (b : ℝ) (h : ∀ x ∈ s, x ≤ b) : BddAbove s := by
  refine ⟨b, ?_⟩
  exact h

/-! ### R2. `refine ⟨a, ?_⟩` on `s.Nonempty` · goal → `a ∈ s`
`s.Nonempty` unfolds to `∃ x, x ∈ s`. In one go: `⟨a, ha⟩`. -/
example (s : Set ℝ) (a : ℝ) (ha : a ∈ s) : s.Nonempty := by
  refine ⟨a, ?_⟩
  exact ha

/-! ### R3. `le_csSup` · `BddAbove s → a ∈ s → a ≤ sSup s` · context gains the inequality -/
example (s : Set ℝ) (a : ℝ) (hb : BddAbove s) (ha : a ∈ s) (P : Prop) (h : a ≤ sSup s → P) : P := by
  have h1 := le_csSup hb ha
  exact h h1

/-! ### R4. `csSup_le` · `s.Nonempty → (∀ x ∈ s, x ≤ b) → sSup s ≤ b` · goal → two goals -/
example (s : Set ℝ) (b : ℝ) (hs : s.Nonempty) (h : ∀ x ∈ s, x ≤ b) : sSup s ≤ b := by
  apply csSup_le
  · exact hs
  · exact h

/-! ## Naming a term; the set `{x | x ∈ Set.Icc a b ∧ p x}` -/

/-! ### R5. `set y := e` · context gains `y : τ := e`; goal: every `e` → `y`
Use it to give `sSup {…}` a short name. `y` is a *local definition*: Lean still knows `y = e`. -/
example (g : ℝ → ℝ) (P : ℝ → Prop) (h : ∀ y, P y) : P (g 0 + 1) := by
  set y := g 0 + 1
  exact h y

/-! ### R6. `refine ⟨⟨?_, ?_⟩, ?_⟩` on `x ∈ {x | x ∈ Set.Icc a b ∧ p x}` · goal → three goals
`x ∈ {x | q x}` means `q x`, and `x ∈ Set.Icc a b` means `a ≤ x ∧ x ≤ b`. -/
example (a b x : ℝ) (p : ℝ → Prop) (h1 : a ≤ x) (h2 : x ≤ b) (h3 : p x) :
    x ∈ {x | x ∈ Set.Icc a b ∧ p x} := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact h1
  · exact h2
  · exact h3

/-! ### R7. `le_rfl` · `a ≤ a` · closes the goal -/
example (a : ℝ) : a ≤ a := by
  exact le_rfl

/-! ### R8. `hx.1.2`, `hx.2` · from `hx : x ∈ {x | x ∈ Set.Icc a b ∧ p x}` · context gains a part
`.1` / `.2` take the left / right side of an `∧`; Lean sees the `∧` through `∈ {…}` and `Set.Icc`
(also when the set has a `set` name such as `S`). -/
example (a b x : ℝ) (p : ℝ → Prop) (hx : x ∈ {x | x ∈ Set.Icc a b ∧ p x}) (P : Prop)
    (h : x ≤ b → p x → P) : P := by
  have hxb := hx.1.2
  have hpx := hx.2
  exact h hxb hpx

/-! ## Proof by contradiction -/

/-! ### R9. `by_contra h` · goal `G` → `False`; context gains `h : ¬G` -/
example (a b : ℝ) (k : ¬a ≤ b → False) : a ≤ b := by
  by_contra h
  exact k h

/-! ### R10. `push Not at h` · context: `h : ¬a ≤ b` → `h : b < a` (pushes `¬` inward) -/
example (a b : ℝ) (h : ¬a ≤ b) (P : Prop) (k : b < a → P) : P := by
  push Not at h
  exact k h

/-! ## Using an ε–δ hypothesis -/

/-- A toy definition whose body is an `∀ ε > 0, ∃ δ > 0, …` (as the exercise's `ContAt`). -/
def EpsDelta (Q : ℝ → ℝ → Prop) : Prop := ∀ ε > 0, ∃ δ > 0, Q ε δ

/-! ### R11. `obtain ⟨δ, hδ, hd⟩ := hg e he` · context: `δ`, `hδ : δ > 0`, `hd : Q e δ`
Applying `hg : EpsDelta Q` to `e` and `he : e > 0` sees through the definition. -/
example (Q : ℝ → ℝ → Prop) (hg : EpsDelta Q) (e : ℝ) (he : e > 0) (P : Prop)
    (k : ∀ δ > 0, Q e δ → P) : P := by
  obtain ⟨δ, hδ, hd⟩ := hg e he
  exact k δ hδ hd

/-! ### R12. `sub_lt_self` · `0 < b → a - b < a` · context gains `a - b < a` -/
example (a b : ℝ) (hb : 0 < b) (P : Prop) (k : a - b < a → P) : P := by
  have hlt := sub_lt_self a hb
  exact k hlt

/-! ### R13. `exists_lt_of_lt_csSup` · `s.Nonempty → b < sSup s → ∃ x ∈ s, b < x` · context
Below the least upper bound there is always an element of `s` above you. -/
example (s : Set ℝ) (b : ℝ) (hs : s.Nonempty) (hb : b < sSup s) (P : Prop)
    (k : ∀ x ∈ s, b < x → P) : P := by
  obtain ⟨x, hxs, hbx⟩ := exists_lt_of_lt_csSup hs hb
  exact k x hxs hbx

/-! ### R14. `abs_lt` · `|a| < b ↔ -b < a ∧ a < b` · goal: `rw [abs_lt]` -/
example (a b : ℝ) (h : -b < a ∧ a < b) : |a| < b := by
  rw [abs_lt]
  exact h

/-! ### R15. `rw [abs_lt] at h` · context: `h : |a| < b` → `h : -b < a ∧ a < b` -/
example (a b : ℝ) (h : |a| < b) (P : Prop) (k : -b < a ∧ a < b → P) : P := by
  rw [abs_lt] at h
  exact k h

/-! ### R16. `linarith` · closes a linear (in)equality that follows by adding up hypotheses
It also reads both sides of an `∧` hypothesis; `linarith [t]` adds the extra fact `t`. -/
example (x y e : ℝ) (h : -e < x - y ∧ x - y < e) (hy : y ≤ 0) : x < e := by
  linarith

/-! ## Moving to the right of `c` -/

/-! ### R17. `lt_of_le_of_ne` · `a ≤ b → a ≠ b → a < b` · goal → `False` with `h : a = b`
`a ≠ b` is `a = b → False`, so it is proved by a function `fun h => …`. -/
example (a b : ℝ) (h1 : a ≤ b) (k : a = b → False) : a < b := by
  refine lt_of_le_of_ne h1 (fun h => ?_)
  exact k h

/-! ### R18. `rw [h] at h'` · context: `h : a = b` rewrites `h' : P a` to `h' : P b` -/
example (a b : ℝ) (P : ℝ → Prop) (h : a = b) (h' : P a) (k : P b → False) : False := by
  rw [h] at h'
  exact k h'

/-! ### R19. `lt_min` · `a < b → a < c → a < min b c` · goal → two goals -/
example (a b c : ℝ) (h1 : a < b) (h2 : a < c) : a < min b c := by
  apply lt_min
  · exact h1
  · exact h2

/-! ### R20. `min_le_left` · `min a b ≤ a` · context gains the inequality -/
example (a b : ℝ) (P : Prop) (k : min a b ≤ a → P) : P := by
  have h := min_le_left a b
  exact k h

/-! ### R21. `min_le_right` · `min a b ≤ b` · context gains the inequality -/
example (a b : ℝ) (P : Prop) (k : min a b ≤ b → P) : P := by
  have h := min_le_right a b
  exact k h

/-! ## Assembling the zero -/

/-! ### R22. `le_antisymm` · `a ≤ b → b ≤ a → a = b` · goal → two goals -/
example (a b : ℝ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  apply le_antisymm
  · exact h1
  · exact h2

/-! ### R23. `refine ⟨x, ⟨?_, ?_⟩, ?_⟩` on `∃ c ∈ Set.Icc a b, P c` · goal → three goals
`∃ c ∈ s, P c` is `∃ c, c ∈ s ∧ P c`. -/
example (a b x : ℝ) (P : ℝ → Prop) (h1 : a ≤ x) (h2 : x ≤ b) (h3 : P x) :
    ∃ c ∈ Set.Icc a b, P c := by
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · exact h1
  · exact h2
  · exact h3

/-! The witness may be written `_` only when a part given in the same `refine` fixes it: here `h1`
mentions `x`, so `⟨_, ⟨h1, h2⟩, ?_⟩` works. `⟨_, ⟨?_, ?_⟩, ?_⟩` is an error ("don't know how to
synthesize placeholder"). -/
example (a b x : ℝ) (P : ℝ → Prop) (h1 : a ≤ x) (h2 : x ≤ b) (h3 : P x) :
    ∃ c ∈ Set.Icc a b, P c := by
  refine ⟨_, ⟨h1, h2⟩, ?_⟩
  exact h3

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Bounding a `sSup` from both sides: R1–R4, R6–R8 on the toy set `{x | x ∈ [0, 2] ∧ x ≤ 1}` -/
example : 0 ≤ sSup {x : ℝ | x ∈ Set.Icc 0 2 ∧ x ≤ 1} ∧ sSup {x : ℝ | x ∈ Set.Icc 0 2 ∧ x ≤ 1} ≤ 2 := by
  set T := {x : ℝ | x ∈ Set.Icc 0 2 ∧ x ≤ 1}
  have h0 : (0 : ℝ) ∈ T := ⟨⟨le_rfl, by norm_num⟩, by norm_num⟩
  constructor
  · exact le_csSup ⟨2, fun x hx => hx.1.2⟩ h0
  · exact csSup_le ⟨0, h0⟩ (fun x hx => hx.1.2)

/-! ### W2. One use of an ε–δ bound: R14, R15, R16 on a toy `g` with `ε = 1` -/
example (g : ℝ → ℝ) (t u δ : ℝ) (hd : ∀ v, |v - t| < δ → |g v - g t| < 1)
    (h1 : t - δ < u) (h2 : u ≤ t) : g t - 1 < g u := by
  have hu := hd u (by rw [abs_lt]; constructor <;> linarith)
  rw [abs_lt] at hu
  linarith

/-! ### W3. A point strictly right of `t` but not past `5`: R5, R19–R21 -/
example (t δ : ℝ) (hδ : 0 < δ) (ht : t < 5) : t < min (t + δ / 2) 5 ∧ min (t + δ / 2) 5 ≤ 5 := by
  set y := min (t + δ / 2) 5
  have hy1 : t < y := lt_min (by linarith) ht
  exact ⟨hy1, min_le_right _ _⟩

end H041Guide

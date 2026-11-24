/- Guide for M073 (x² is continuous (ε-δ)).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the map `y ↦ 3 * y`, a bound on `|y|`).
Assumed: Lean basics.
-/
import Mathlib

namespace M073Guide

/-! # Part R · Reference entries -/

/-! ## Opening the ε-δ statement -/

/-! ### R1. `intro ε hε` · goal: a definition whose body is `∀ ε > 0, …` → context gains `ε`, `hε`
`intro` unfolds a definition by itself when its body starts with `∀`. `∀ ε > 0, Q ε` is
`∀ ε, ε > 0 → Q ε`, so it takes two names. -/
def AllPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε

example (Q : ℝ → Prop) (h : ∀ ε, ε > 0 → Q ε) : AllPos Q := by
  intro ε hε
  exact h ε hε

/-! ### R2. `refine ⟨d, ?_, fun y hy => ?_⟩` · goal `∃ δ > 0, ∀ y, R δ y → S y` → goal list: `d > 0`, then `S y`
`∃ δ > 0, G δ` is `∃ δ, δ > 0 ∧ G δ`; the anonymous constructor `⟨…⟩` fills the witness `d`, the
proof of `d > 0`, and the `∀ y, … → …` part in one go. Any `?_` can be a proof on the spot (`by positivity`). -/
example (d : ℝ) (R : ℝ → ℝ → Prop) (S : ℝ → Prop) (hd : d > 0) (h : ∀ y, R d y → S y) :
    ∃ δ > 0, ∀ y, R δ y → S y := by
  refine ⟨d, ?_, fun y hy => ?_⟩
  exact hd
  exact h y hy

/-! ### R3. `positivity` · closes `0 < e`, `e > 0`, `0 ≤ e`, `e ≠ 0` when `e` is built from positive pieces
It knows `0 ≤ |b|`, numerals, `+`, `*`, `/`, `min`, and uses hypotheses `hε : ε > 0` about atoms. -/
example (ε b : ℝ) (hε : ε > 0) : min 2 (ε / (|b| + 3)) > 0 := by
  positivity

/-! ### R4. `beta_reduce` · goal: `(fun x => t x) y` → `t y` (optional: `calc` sees through it anyway) -/
example (f : ℝ → ℝ) (y : ℝ) (P : ℝ → Prop) (h : P (f y ^ 3)) : P ((fun x => f x ^ 3) y) := by
  beta_reduce
  exact h

/-! ## Using `|y - x| < min b c` -/

/-! ### R5. `min_le_left`, `min_le_right` · `min a b ≤ a`, `min a b ≤ b` · context gains the fact -/
example {α : Type} [LinearOrder α] (a b : α) (P : Prop) (h : min a b ≤ a → min a b ≤ b → P) : P := by
  have ha : min a b ≤ a := min_le_left a b
  have hb : min a b ≤ b := min_le_right a b
  exact h ha hb

/-! ### R6. `lt_of_lt_of_le` · `x < m → m ≤ b → x < b` · context gains `x < b` -/
example {α : Type} [Preorder α] (x m b : α) (hx : x < m) (hm : m ≤ b) (P : Prop) (h : x < b → P) :
    P := by
  have h1 : x < b := lt_of_lt_of_le hx hm
  exact h h1

/-! ## Chains of (in)equalities -/

/-! ### R7. `calc` · goal `a < d` → one goal per step (`a = b`, `b ≤ c`, `c < d`)
Each step is `_ rel rhs := proof`; `_` is the previous right-hand side. Mixing `=`, `≤`, `<` gives `<`.
Here `refine calc … := ?_` leaves the steps as goals so you can see them; normally write `:= by …`. -/
example (a b c d : ℝ) (h1 : a = b) (h2 : b ≤ c) (h3 : c < d) : a < d := by
  refine calc a = b := ?_
    _ ≤ c := ?_
    _ < d := ?_
  exacts [h1, h2, h3]

/-! ### R8. `ring_nf` under `|·|` · goal: the ring expression inside `|…|` is normalised
`ring` cannot prove `|u - v| = |(u + v) - 2 * v|` itself (it treats `|·|` as an unknown function); it
falls back to `ring_nf` and prints "Try this: ring_nf". `ring_nf` normalises the arguments, so both
sides become `|u - v|` and the goal closes by itself. -/
example (u v : ℝ) (P : ℝ → Prop) (h : P |u - v|) : P |(u + v) - 2 * v| := by
  ring_nf
  exact h

/-! ## Absolute values -/

/-! ### R9. `abs_add_le` · `|a + b| ≤ |a| + |b|` (triangle inequality) · context gains the fact
On `ℝ`; in general `{α : Type} [Lattice α] [AddCommGroup α] [AddLeftMono α]`. -/
example (a b : ℝ) (P : Prop) (h : |a + b| ≤ |a| + |b| → P) : P := by
  have ht : |a + b| ≤ |a| + |b| := abs_add_le a b
  exact h ht

/-! ### R10. `abs_mul` · `|a * b| = |a| * |b|`; `rw [← abs_mul]` merges two absolute values -/
example {α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (a b : α) (P : α → Prop)
    (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R11. `abs_two` · `|2| = 2` · goal -/
example {α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (b : α) (P : α → Prop)
    (h : P (2 * b)) : P (|2| * b) := by
  rw [abs_two]
  exact h

/-! ## Closing inequalities -/

/-! ### R12. `linarith` · closes a linear (in)equality that follows from hypotheses
Atoms such as `|t|` are treated as unknowns, so `|t| < 1 ⊢ |t| + c ≤ c + 1` is linear. -/
example (t c : ℝ) (h : |t| < 1) : |t| + c ≤ c + 1 := by
  linarith

/-! ### R13. `gcongr` on `≤` · goal `z * x ≤ z * y` → goal `x ≤ y`; side goal `0 ≤ z` by `positivity`
`gcongr` compares the parts that differ. It closes the remaining goal itself when a hypothesis
states it (`x ≤ y` or `x < y` in the context); here it cannot, so `x ≤ y` is left. -/
example (t x y : ℝ) (h : x + 0 ≤ y) : |t| * x ≤ |t| * y := by
  gcongr
  linarith

/-! ### R14. `gcongr` on `<` · goal `x * c < y * c` → goal `x < y`; side goal `0 < c` by `positivity` -/
example (x y b : ℝ) (h : x + 0 < y) : x * (|b| + 1) < y * (|b| + 1) := by
  gcongr
  linarith

/-! ### R15. `field_simp` · closes `x / c * c = x` once it can show `c ≠ 0` (here `|b| + 1 ≠ 0`) -/
example (x b : ℝ) : x / (|b| + 1) * (|b| + 1) = x := by
  field_simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. ε-δ for `y ↦ 3 * y` at `c`, with `δ = ε / 3`: R1, R2, R3, R7, R10, R8, R14, R15 -/
example (c : ℝ) : ∀ ε > 0, ∃ δ > 0, ∀ y, |y - c| < δ → |3 * y - 3 * c| < ε := by
  intro ε hε
  refine ⟨ε / 3, by positivity, fun y hy => ?_⟩
  calc |3 * y - 3 * c| = |3 * (y - c)| := by ring_nf
    _ = |3| * |y - c| := by rw [abs_mul]
    _ = 3 * |y - c| := by norm_num
    _ < 3 * (ε / 3) := by gcongr
    _ = ε := by field_simp

/-! ### W2. A bound from `|y - c| < min 1 _`: R5 → R6, then R7 with R8, R9, R12 -/
example (c ε y : ℝ) (hy : |y - c| < min 1 (ε / 4)) : |y| ≤ |c| + 1 := by
  have h1 : |y - c| < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  calc |y| = |(y - c) + c| := by ring_nf
    _ ≤ |y - c| + |c| := abs_add_le _ _
    _ ≤ |c| + 1 := by linarith

end M073Guide

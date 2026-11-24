/- Guide for M112 (Truncating the exponential series).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`x = 1/4`, two terms).
Assumed: Lean basics.
-/
import Mathlib

namespace M112Guide

/-! # Part R · Reference entries -/

/-! ## The remainder bound as a hypothesis -/

/-! ### R1. `have h := Real.exp_bound hx hn` · context gains the remainder bound `h`
`Real.exp_bound : |x| ≤ 1 → 0 < n → |exp x - ∑ m ∈ range n, x ^ m / m!| ≤ |x| ^ n * ((n+1) / (n! * n))`.
`have h := e` (no type written) adds `h` with whatever type the term `e` has. -/
example (x : ℝ) (n : ℕ) (hx : |x| ≤ 1) (hn : 0 < n) (G : Prop) (g : G) : G := by
  have h := Real.exp_bound hx hn
  exact g

/-! ### R2. Named arguments `(x := a)`, `(n := k)` · context gains the bound for a chosen `n`
`x` and `n` are implicit in `Real.exp_bound`; `(n := 4)` fixes one by name. A side condition such as
`0 < 4` is passed as `(by norm_num)`. -/
example (a : ℝ) (ha : |a| ≤ 1) (G : Prop) (g : G) : G := by
  have h := Real.exp_bound (x := a) ha (n := 4) (by norm_num)
  exact g

/-! ### R3. `abs_of_pos` · `0 < a → |a| = a` · goal: `|a|` → `a` -/
example (a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ## Expanding a finite sum -/

/-! ### R4. `Finset.sum_range_succ` · goal: peel off the last term of a sum over `range (n + 1)` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∑ m ∈ Finset.range n, f m + f n)) : P (∑ m ∈ Finset.range (n + 1), f m) := by
  rw [Finset.sum_range_succ]
  exact h

/-! ### R5. `Finset.sum_range_zero` · goal: the empty sum `∑ m ∈ range 0, f m` → `0` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (P : M → Prop) (h : P 0) :
    P (∑ m ∈ Finset.range 0, f m) := by
  rw [Finset.sum_range_zero]
  exact h

/-! ## Evaluating the numbers -/

/-! ### R6. `norm_num [Nat.factorial]` · goal: a factorial of a numeral → its value -/
example (P : ℝ → Prop) (h : P 6) : P ((Nat.factorial 3 : ℕ) : ℝ) := by
  norm_num [Nat.factorial]
  exact h

/-! ### R7. `norm_num` · goal: `Nat.succ k` and casts `↑k` of numerals → numerals -/
example (P : ℝ → Prop) (h : P (4 / 3)) : P ((Nat.succ 3 : ℕ) / (3 : ℕ)) := by
  norm_num
  exact h

/-! ### R8. `norm_num [lemmas] at h ⊢` · context and goal: both simplified the same way -/
example (x : ℝ) (h : x - ((Nat.factorial 3 : ℕ) : ℝ) ≤ 2 * 3) : x - 6 ≤ 6 := by
  norm_num [Nat.factorial] at h ⊢
  exact h

/-! ### R9. `linarith` · closes a linear (in)equality that follows from the hypotheses
Anything that is not `+`, `-`, a numeral times something, `≤`, `<`, `=` is an atom: here `|x - y|`. -/
example (x y : ℝ) (h : |x - y| ≤ 1 / 4) : |x - y| < 1 / 2 := by linarith

/-! ## Absolute values and decimals -/

/-! ### R10. `abs_le` · `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b`; `.mp` uses it left to right · context gains `h` -/
example (a b : ℝ) (hab : |a| ≤ b) (G : Prop) (g : -b ≤ a ∧ a ≤ b → G) : G := by
  have h := abs_le.mp hab
  exact g h

/-! ### R11. Decimal literals · `norm_num` turns `1.59` into the fraction `159 / 100` (in lowest terms) -/
example (P : ℝ → Prop) (h : P (159 / 100)) : P 1.59 := by
  norm_num
  exact h

/-! ### R12. `h.1`, `h.2` (`And.left`, `And.right`) · context gains one side of `h : A ∧ B` -/
example (A B : Prop) (h : A ∧ B) (G : Prop) (g : B → G) : G := by
  have h2 := h.2
  exact g h2

/-! ### R13. `linarith [t₁, t₂]` · closes, using the extra facts `tᵢ` (proof terms) as hypotheses -/
example (x : ℝ) (f : ∀ y : ℝ, y ≤ y ^ 2 + 1) : x ≤ x ^ 2 + 2 := by linarith [f x]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Two terms of the series at `x = 1/4`: `1 + 1/4 = 5/4`, remainder `(1/4)² · 3/(2!·2) = 3/64` -/
example : |Real.exp (1 / 4) - 5 / 4| ≤ 3 / 64 := by
  have h := Real.exp_bound (x := 1 / 4) (by norm_num [abs_of_pos]) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-! ### W2. From an absolute-value bound to decimal bounds: R10, `constructor`, R11, R13 -/
example (h0 : |Real.exp (1 / 4) - 5 / 4| ≤ 3 / 64) :
    1.2 < Real.exp (1 / 4) ∧ Real.exp (1 / 4) < 1.3 := by
  have h := abs_le.mp h0
  constructor
  all_goals norm_num
  all_goals linarith [h.1, h.2]

end M112Guide

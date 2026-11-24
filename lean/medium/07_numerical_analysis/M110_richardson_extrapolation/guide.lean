/- Guide for M110 (Richardson extrapolation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (step `h / 3`, weight `3 ^ n`).
Assumed: Lean basics.
-/
import Mathlib

namespace M110Guide

/-! # Part R · Reference entries -/

/-! ## Facts about `2 ^ p` -/

/-! ### R1. `one_lt_pow₀` · `1 < a → n ≠ 0 → 1 < a ^ n` · goal → two goals (with `apply`) -/
example {α : Type} [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (a : α) (n : ℕ)
    (ha : 1 < a) (hn : n ≠ 0) : 1 < a ^ n := by
  apply one_lt_pow₀
  exact ha
  exact hn

/-! ### R2. `omega` · closes linear arithmetic over `ℕ` / `ℤ` from the context -/
example (n : ℕ) (hn : 1 ≤ n) : n ≠ 0 := by
  omega

/-! ### R3. `linarith` · closes a linear (in)equality over `ℝ` that follows from the context -/
example (a : ℝ) (ha : 1 < a) : 0 < a - 1 := by
  linarith

/-! ## Using the hypothesis `∀ t, 0 < t → …` -/

/-! ### R4. `have e := hQ t ht` · context gains the instance `e : Q t` -/
example (Q : ℝ → Prop) (hQ : ∀ t, 0 < t → Q t) (t : ℝ) (ht : 0 < t) (G : Prop) (g : Q t → G) :
    G := by
  have e := hQ t ht
  exact g e

/-! ### R5. `positivity` · closes `0 < e` / `0 ≤ e` by the shape of `e` (uses `0 < x` facts on atoms) -/
example (t : ℝ) (ht : 0 < t) (n : ℕ) : 0 < 2 ^ n * (t / 2) := by
  positivity

/-! ## Naming the remainders -/

/-! ### R6. `set u := e with hu` · context gains `u := e`, `hu : u = e`; every `e` (goal and context) → `u` -/
example (f : ℝ → ℝ) (a b : ℝ) (P : ℝ → Prop) (hb : P (f a - b)) : P (f a - b) := by
  set u := f a - b with hu
  exact hb

/-! ## The cancellation identity -/

/-! ### R7. `div_pow` · `(a / b) ^ n = a ^ n / b ^ n` · goal -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n / b ^ n)) :
    P ((a / b) ^ n) := by
  rw [div_pow]
  exact h

/-! ### R8. `field_simp` · goal: denominators cleared, using `b ≠ 0` / `0 < b` facts in the context -/
example (a b c : ℝ) (hb : b ≠ 0) (h : a = b * c) : a / b = c := by
  field_simp
  exact h

/-! ### R9. `ring` · closes an identity of commutative rings (here: `c * x` cancels) -/
example (a c x y z : ℝ) : a * (y - c * x) - (z - c * (a * x)) = a * y - z := by
  ring

/-! ## Absolute value of a quotient -/

/-! ### R10. `abs_div` · `|a / b| = |a| / |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R11. `abs_of_pos` · `0 < a → |a| = a` · goal -/
example (a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ### R12. `div_le_iff₀` · `0 < c → (b / c ≤ a ↔ b ≤ a * c)` · goal: the denominator moves right -/
example (a b c : ℝ) (hc : 0 < c) (h : b ≤ a * c) : b / c ≤ a := by
  rw [div_le_iff₀ hc]
  exact h

/-! ## Chaining inequalities -/

/-! ### R13. `calc` · goal `a ≤ c` → one goal per step; a step written `:= ?_` stays open -/
example (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  calc a ≤ b := hab
    _ ≤ c := ?_
  exact hbc

/-! ### R14. `abs_sub` · `|a - b| ≤ |a| + |b|` (a term: use it as a `calc` step or with `exact`) -/
example (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  exact abs_sub a b

/-! ### R15. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R16. `rw [lemma] at e` · context: hypothesis `e` rewritten; goal unchanged -/
example (a b x : ℝ) (n : ℕ) (e : x ≤ (a / b) ^ n) (h : x ≤ a ^ n / b ^ n → False) : False := by
  rw [div_pow] at e
  exact h e

/-! ### R17. `gcongr` · goal `k * a + b ≤ k * c + d` → goals `a ≤ c`, `b ≤ d`
It closes what `assumption` proves (`hac` here) and `0 ≤ k` by `positivity`; the rest stays open. -/
example (k a b c d : ℝ) (hk : 0 < k) (hac : a ≤ c) (hb : b ≤ 0) (hd : 0 ≤ d) :
    k * a + b ≤ k * c + d := by
  gcongr
  linarith

/-! ### R18. `field_simp` as a finisher · closes an identity once its denominators are cleared -/
example (a b c : ℝ) (hb : 0 < b) : (a / b + c) * b = a + c * b := by
  field_simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A cancellation with step `t / 3` and weight `3 ^ n`: R7, then R8 as a finisher (R18) -/
example (n : ℕ) (t c y : ℝ) :
    3 ^ n * (y - c * (t / 3) ^ n) = 3 ^ n * y - c * t ^ n := by
  rw [div_pow]
  field_simp

/-! ### W2. Clearing a positive denominator under `|·|`: R10, R11, R12 -/
example (x k : ℝ) (hk : 0 < k) (h : |x| ≤ 5 * k) : |x / k| ≤ 5 := by
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  exact h

/-! ### W3. Triangle inequality, then plug in bounds: R13, R14, R15, R11 with R5, R17 -/
example (n : ℕ) (x y a b : ℝ) (hx : |x| ≤ a) (hy : |y| ≤ b) :
    |3 ^ n * x - y| ≤ 3 ^ n * a + b := by
  calc |3 ^ n * x - y| ≤ |3 ^ n * x| + |y| := abs_sub _ _
    _ = 3 ^ n * |x| + |y| := by rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ 3 ^ n * a + b := by gcongr

end M110Guide

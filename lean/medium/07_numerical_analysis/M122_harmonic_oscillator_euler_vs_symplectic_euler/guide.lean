/- Guide for M122 (Harmonic oscillator: Euler vs symplectic Euler).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a doubling map, a shear map
with the invariant `x - y²`, the bound `2xy ≤ x² + y²`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M122Guide

/-- A two-component recursion used only in this guide. A state is a pair `(x, y) : ℝ × ℝ`; the
update rules `f` and `g` are placeholders: step `n + 1` is `(f x y, g x y)` with `(x, y)` = step `n`. -/
def orbit (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x₀, y₀)
  | n + 1 => (f (orbit f g x₀ y₀ n).1 (orbit f g x₀ y₀ n).2,
              g (orbit f g x₀ y₀ n).1 (orbit f g x₀ y₀ n).2)

/-- The same with a `let`: the new second component `y'` is computed first, and the new first
component uses `y'` (not the old `y`). -/
def leap (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x₀, y₀)
  | n + 1 =>
    let y' := g (leap f g x₀ y₀ n).1 (leap f g x₀ y₀ n).2
    (f (leap f g x₀ y₀ n).1 y', y')

/-! # Part R · Reference entries -/

/-! ## Induction on the step count -/

/-! ### R1. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: `P n` → `P 0` and `P (n + 1)`, plus `ih : P n`
Usually you write the proof right after each `=>`; `?_` leaves the two goals open so you can see them. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ### R2. `simp [d]` on step `0` · closes the base case
It applies the equation `d … 0 = (x₀, y₀)`, the projections `(a, b).1 = a`, `(a, b).2 = b`, and
cleans up `a ^ 0 = 1` (`pow_zero`) and `1 * a = a` (`one_mul`). -/
example (f g F : ℝ → ℝ → ℝ) (x₀ y₀ c : ℝ) :
    F (orbit f g x₀ y₀ 0).1 (orbit f g x₀ y₀ 0).2 = c ^ 0 * F x₀ y₀ := by
  simp [orbit]

/-! ### R3. `simp only [d]` on step `n + 1` · goal: one step of the recursion is unfolded
The projection `.1` of the new pair is taken at once; step `n` stays folded, so `ih` still matches. -/
example (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) (n : ℕ) (P : ℝ → Prop)
    (h : P (f (orbit f g x₀ y₀ n).1 (orbit f g x₀ y₀ n).2)) : P (orbit f g x₀ y₀ (n + 1)).1 := by
  simp only [orbit]
  exact h

/-! ### R4. `linear_combination e * ih` · closes `lhs = rhs` when `lhs - rhs - e * (ih.lhs - ih.rhs)` is `0` by `ring` -/
example (a b e r : ℝ) (ih : a = b) : e * a + r = e * b + r := by
  linear_combination e * ih

/-! ## A conserved quantity -/

/-! ### R5. `rw [← ih]` with `ih : E n = c` · goal: the constant `c` → `E n`
Every `c` in the goal is replaced, so `E (n + 1) = c` becomes the one-step claim `E (n + 1) = E n`. -/
example (E : ℕ → ℝ) (c : ℝ) (n : ℕ) (ih : E n = c) (h : E (n + 1) = E n) : E (n + 1) = c := by
  rw [← ih]
  exact h

/-! ### R6. `simp only [d]` when the step has a `let` · goal: the step is unfolded and `y'` is inlined -/
example (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) (n : ℕ) (P : ℝ → Prop)
    (h : P (f (leap f g x₀ y₀ n).1 (g (leap f g x₀ y₀ n).1 (leap f g x₀ y₀ n).2))) :
    P (leap f g x₀ y₀ (n + 1)).1 := by
  simp only [leap]
  exact h

/-! ## Using a proved theorem, naming subterms -/

/-! ### R7. `have hS := thm n` · context gains `thm` at the argument `n` -/
example (E : ℕ → ℝ) (c : ℝ) (thm : ∀ n, E n = c) (n : ℕ) (P : Prop) (k : E n = c → P) : P := by
  have hS := thm n
  exact k hS

/-! ### R8. `set x := e` · goal and context: every `e` becomes `x`; context gains `x : ℝ := e`
`set x := e with hx` also adds `hx : x = e`. -/
example (s : ℕ → ℝ × ℝ) (n : ℕ) (P : ℝ → Prop) (hP : P (s n).1) : P (s n).1 := by
  set x := (s n).1
  exact hP

/-! ### R9. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · context gains the product fact -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (P : Prop) (k : 0 ≤ a * b → P) : P := by
  have hc : 0 ≤ a * b := mul_nonneg ha hb
  exact k hc

/-! ### R10. `sq_nonneg` · `0 ≤ a ^ 2` for every `a` · context gains the fact -/
example (a b : ℝ) (P : Prop) (k : 0 ≤ (a - b) ^ 2 → P) : P := by
  have hq := sq_nonneg (a - b)
  exact k hq

/-! ## Clearing a fraction -/

/-! ### R11. `div_mul_eq_mul_div` · `a / b * c = a * c / b` · goal -/
example {α : Type} [DivisionCommMonoid α] (a b c : α) (P : α → Prop) (h : P (a * c / b)) :
    P (a / b * c) := by
  rw [div_mul_eq_mul_div]
  exact h

/-! ### R12. `le_div_iff₀` · `0 < c → (a ≤ b / c ↔ a * c ≤ b)` · goal rewritten, plus side goal `0 < c`
Write `rw [le_div_iff₀ (by linarith)]` to close the side goal on the spot. -/
example (a b c : ℝ) (h : a * c ≤ b) (hc : 0 < c) : a ≤ b / c := by
  rw [le_div_iff₀]
  exact h
  exact hc

/-! ## Closing (in)equalities -/

/-! ### R13. `linarith` · closes a linear (in)equality that follows from the context -/
example (a : ℝ) (ha : a < 2) : 0 < 2 - a := by
  linarith

/-! ### R14. `nlinarith [t₁, t₂]` · closes goals that need products of hypotheses and the facts `tᵢ`
Here it multiplies `hc` by the hint `0 ≤ (a - b) ^ 2`; `linarith [sq_nonneg (a - b)]` fails. -/
example (a b c : ℝ) (hc : 0 ≤ c) : 2 * c * a * b ≤ c * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-! # Part W · Worked combinations (not the exercise's objects)
After the base case is closed with `·`, the remaining tactics work on the `succ` goal, so the
infoview shows each state of the step. -/

/-! ### W1. Doubling both components multiplies `x² + y²` by 4 each step: R1, R2, R3, R4 -/
example (x₀ y₀ : ℝ) (n : ℕ) :
    (orbit (fun x _ => 2 * x) (fun _ y => 2 * y) x₀ y₀ n).1 ^ 2
      + (orbit (fun x _ => 2 * x) (fun _ y => 2 * y) x₀ y₀ n).2 ^ 2 = 4 ^ n * (x₀ ^ 2 + y₀ ^ 2) := by
  induction n with | zero => ?_ | succ n ih => ?_
  · simp [orbit]
  simp only [orbit]
  linear_combination 4 * ih

/-! ### W2. The shear `y' = y + 1`, `x' = x + 2y' - 1` conserves `x - y²`: R1, R2, R5, R6, `ring` -/
example (x₀ y₀ : ℝ) (n : ℕ) :
    (leap (fun x y' => x + 2 * y' - 1) (fun _ y => y + 1) x₀ y₀ n).1
      - (leap (fun x y' => x + 2 * y' - 1) (fun _ y => y + 1) x₀ y₀ n).2 ^ 2 = x₀ - y₀ ^ 2 := by
  induction n with | zero => ?_ | succ n ih => ?_
  · simp [leap]
  rw [← ih]
  simp only [leap]
  ring

/-! ### W3. From a conserved `x² + y² = c` to the bound `xy ≤ c/2`: R7, R8, R11, R12, R14 -/
example (s : ℕ → ℝ × ℝ) (c : ℝ) (thm : ∀ n, (s n).1 ^ 2 + (s n).2 ^ 2 = c) (n : ℕ) :
    (s n).1 * (s n).2 ≤ 1 / 2 * c := by
  have hS := thm n
  set x := (s n).1
  set y := (s n).2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
  nlinarith [sq_nonneg (x - y)]

end M122Guide

/- Guide for M106 (Bisection invariants).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (an orbit `x, g x, g (g x), …`,
a trisection step).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M106Guide

/-! # Part R · Reference entries -/

/-! ## Induction on the step count -/

/-! ### R1. `induction n with | zero => … | succ n ih => …` · goal → two goals; context gains `n ih`
Writing `?_` as each alternative's body leaves both goals open, so you can see them; in a proof
you write the tactics for that case after `=>`. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => ?_
    | succ n ih => ?_
  exact h0
  exact hs n ih

/-! ### R2. `simp only [D]` on a recursive `def` · goal: `D … 0` / `D … (n + 1)` → that clause's body
`simp only [orbit]` rewrites with the defining equations (one per `|` clause). It fires only where the
argument is literally `0` or `n + 1`: `orbit g x n` with a variable `n` stays as it is. -/
def orbit {α : Type} (g : α → α) (x : α) : ℕ → α
  | 0 => x
  | n + 1 => g (orbit g x n)

example {α : Type} (g : α → α) (x : α) (n : ℕ) (P : α → Prop) (h : P (g (orbit g x n))) :
    P (orbit g x (n + 1)) := by
  simp only [orbit]
  exact h

example {α : Type} (g : α → α) (x : α) (P : α → Prop) (h : P x) : P (orbit g x 0) := by
  simp only [orbit]
  exact h

/-! ### R3. `pow_zero`, `div_one` · goal: `a / 2 ^ 0` → `a / 1` → `a` (`simp` applies both itself) -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a / 2 ^ 0) := by
  rw [pow_zero]
  rw [div_one]
  exact h

/-! ## The step case -/

/-! ### R4. `obtain ⟨h1, h2, h3⟩ := h` · context: `h : A ∧ B ∧ C` → three hypotheses -/
example (A B C G : Prop) (h : A ∧ B ∧ C) (g : A → B → C → G) : G := by
  obtain ⟨h1, h2, h3⟩ := h
  exact g h1 h2 h3

/-! ### R5. `simp only [D]` on a `def` whose body is an `if` · goal: `D …` → `if c then … else …`
`[Decidable c]` says `c` can be tested, which `if` needs; `x ≤ y` on `ℝ` has an instance. -/
def swapIf {α : Type} (c : Prop) [Decidable c] (p : α × α) : α × α :=
  if c then (p.2, p.1) else p

example {α : Type} (c : Prop) [Decidable c] (p : α × α) (P : α × α → Prop)
    (h : P (if c then (p.2, p.1) else p)) : P (swapIf c p) := by
  simp only [swapIf]
  exact h

/-! ### R6. `split_ifs with hc` · goal list: one goal per branch; context gains `hc : c` / `hc : ¬c`
It finds the `if` anywhere in the goal, here under a projection `.1`. The projections stay. -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hx : P x) (hy : P y) :
    P (if c then (x, y) else (y, x)).1 := by
  split_ifs with hc
  · exact hx
  · exact hy

/-! ### R7. `simp only` (no lemmas) · goal: `(x, y).1` → `x`, `(x, y).2` → `y` -/
example {α β : Type} (x : α) (y : β) (P : α → β → Prop) (h : P x y) : P (x, y).1 (x, y).2 := by
  simp only
  exact h

/-! ### R8. `pow_succ` · `a ^ (n + 1) = a ^ n * a` -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R9. `div_div` · `a / b / c = a / (b * c)`; used right to left: `rw [← div_div]` -/
example {α : Type} [DivisionCommMonoid α] (a b c : α) (P : α → Prop) (h : P (a / b / c)) :
    P (a / (b * c)) := by
  rw [← div_div]
  exact h

/-! ### R10. `ring` · closes a commutative-ring identity; in `ℝ` division by a numeral (`/ 2`) is fine -/
example (x y : ℝ) : x - (x - y) / 2 = (x + y) / 2 := by ring

/-! ### R11. `linarith` · closes a linear `≤ / < / =` goal from the hypotheses in context
It also reads a negated comparison: `¬x ≤ 0` counts as `0 < x`. -/
example (x : ℝ) (h : ¬x ≤ 0) : 0 ≤ x := by
  linarith

example (x y : ℝ) (h : x ≤ y) : x ≤ (x + y) / 2 := by
  linarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A closed form by induction: R1, R2, R3 in the base case; R2, R8, R9, `rw [← ih]` after -/
example (x : ℝ) (n : ℕ) : orbit (fun t => t / 2) x n = x / 2 ^ n := by
  induction n with
    | zero => simp [orbit]
    | succ n ih =>
      simp only [orbit]
      rw [pow_succ, ← div_div, ← ih]

/-! The same step case, one tactic per line, so each state shows in the infoview. The last `rw`
closes the goal because `rw` tries `rfl` afterwards. -/
example (x : ℝ) (n : ℕ) (ih : orbit (fun t => t / 2) x n = x / 2 ^ n) :
    orbit (fun t => t / 2) x (n + 1) = x / 2 ^ (n + 1) := by
  simp only [orbit]
  rw [pow_succ]
  rw [← div_div]
  rw [← ih]

/-! ### W2. One loop step: R5, R6, R7, R11 (a trisection step keeps an end point in order) -/
noncomputable def trisect (c : Prop) [Decidable c] (I : ℝ × ℝ) : ℝ × ℝ :=
  if c then ((2 * I.1 + I.2) / 3, I.2) else (I.1, (I.1 + 2 * I.2) / 3)

example (c : Prop) [Decidable c] (I : ℝ × ℝ) (h : I.1 ≤ I.2) : I.1 ≤ (trisect c I).1 := by
  simp only [trisect]
  split_ifs
  · simp only
    linarith
  · simp only
    linarith

/-! ### W3. Strengthen first: `0 ≤ xₙ` is what makes `xₙ₊₁ ≤ xₙ` go through
The claim about step `n + 1` alone is not inductive; prove a `∀ n` fact by induction, then use it. -/
example (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    orbit (fun t => t / 2) x (n + 1) ≤ orbit (fun t => t / 2) x n := by
  have inv : ∀ k, 0 ≤ orbit (fun t => t / 2) x k := by
    intro k
    induction k with
    | zero =>
      simp only [orbit]
      exact hx
    | succ k ih =>
      simp only [orbit]
      linarith
  have h0 := inv n
  simp only [orbit]
  linarith

end M106Guide

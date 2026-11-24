/- Guide for M119 (Discrete Gronwall inequality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other recursions, other bounds).
Assumed: Lean basics.
-/
import Mathlib

namespace M119Guide

/-! # Part R · Reference entries -/

/-! ## Induction on a strengthened claim -/

/-! ### R1. `induction n with | zero => … | succ k ih => …` · goal → two goals; `succ` gains `ih`
Inside a `have key : ∀ n, Q n := by intro n; induction n with …` this proves a claim of your choice.
The second example leaves both goals open (Mathlib's `induction'`) so the infoview shows them. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => exact h0
    | succ k ih => exact hs k ih

example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction' n with k ih
  exact h0
  exact hs k ih

/-! ### R2. `simp` on a base case · goal: `c ^ 0`, `↑0` cleaned up
Lemmas it uses: `pow_zero` (`c ^ 0 = 1`), `Nat.cast_zero` (`↑(0 : ℕ) = (0 : ℝ)`), `zero_mul`,
`add_zero`, `one_mul`. On a goal `x ≤ x` it also closes it (`le_refl`). -/
example (x c b : ℝ) (P : ℝ → Prop) (h : P x) : P (c ^ 0 * (x + ((0 : ℕ) : ℝ) * b)) := by
  simp
  exact h

/-! ## Facts for the induction step -/

/-! ### R3. `one_le_pow₀` · `1 ≤ a → 1 ≤ a ^ n` · context gains the fact via `have` -/
example (x : ℝ) (n : ℕ) (hx : 1 ≤ x) (G : Prop) (g : 1 ≤ x ^ n → G) : G := by
  have h1 : 1 ≤ x ^ n := one_le_pow₀ hx
  exact g h1

/-! ### R4. `linarith` · closes a goal that follows linearly from the hypotheses
Inline form: `(by linarith : (0 : ℝ) ≤ 1 + x)` is a proof term of that type. -/
example (x : ℝ) (hx : 0 ≤ x) : 1 ≤ 1 + x := by
  linarith

/-! ## Chains of inequalities -/

/-! ### R5. `calc` · goal `x ≤ z` → one goal per step (`_` is the previous right-hand side)
Each step is `_ ≤ rhs := proof`; `=` steps may be mixed in. Here `?_` leaves each step as a goal. -/
example (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  calc x ≤ y := ?_
    _ ≤ z := ?_
  exact h1
  exact h2

/-! ### R6. `gcongr` · goal `c * x + d ≤ c * y + d` → `x ≤ y`
It strips the matching context. The side goal `0 ≤ c` comes from a hypothesis (or `positivity`);
the main goal `x ≤ y` is closed right away when a hypothesis states it exactly. -/
example (c d x w y : ℝ) (hc : 0 ≤ c) (hxw : x ≤ w) (hwy : w ≤ y) : c * x + d ≤ c * y + d := by
  gcongr
  linarith

/-! ### R7. `push_cast` · goal: a cast of a sum `↑(n + 1)` → `↑n + 1` (`Nat.cast_add`, `Nat.cast_one`) -/
example (n : ℕ) (b : ℝ) (P : ℝ → Prop) (h : P ((↑n + 1) * b)) : P (((n + 1 : ℕ) : ℝ) * b) := by
  push_cast
  exact h

/-! ### R8. `pow_succ` · `a ^ (n + 1) = a ^ n * a` -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R9. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · context gains a product fact -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) (G : Prop) (g : a * b ≤ a * c → G) : G := by
  have h := mul_le_mul_of_nonneg_left hbc ha
  exact g h

/-! ### R10. `nlinarith [t₁, …]` · closes a polynomial inequality
It adds the listed facts and pairwise products of hypotheses, then runs `linarith`. Hand it the
product fact it cannot guess (R9). -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) : x ≤ x * y := by
  nlinarith [mul_le_mul_of_nonneg_left hy hx]

/-! ## From `(1 + a) ^ n` to `exp` -/

/-! ### R11. `gcongr` on a right factor · goal `x * s ≤ y * s` → `x ≤ y`
The side goal `0 ≤ s` is proved by `positivity`, which uses hypotheses `0 ≤ u` and knows `0 ≤ ↑n`. -/
example (x y u v : ℝ) (n : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hxw : x ≤ 2) (h2 : 2 ≤ y) :
    x * (u + n * v) ≤ y * (u + n * v) := by
  gcongr
  linarith

/-! ### R12. `gcongr` on powers · goal `x ^ n ≤ y ^ n` → `x ≤ y` (side goal `0 ≤ x`) -/
example (x y : ℝ) (n : ℕ) (hx : 0 ≤ x) (hxw : x ≤ 2) (h2 : 2 ≤ y) : x ^ n ≤ y ^ n := by
  gcongr
  linarith

/-! ### R13. `Real.add_one_le_exp` · `∀ x : ℝ, x + 1 ≤ Real.exp x` · context gains the fact
Pass it to `linarith` directly: `linarith [Real.add_one_le_exp t]`. -/
example (t : ℝ) : t ≤ Real.exp t - 1 := by
  have h := Real.add_one_le_exp t
  linarith

/-! ### R14. `Real.exp_nat_mul` · `Real.exp (↑n * x) = Real.exp x ^ n`; right to left: `rw [← …]` -/
example (x : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (Real.exp (↑n * x))) : P (Real.exp x ^ n) := by
  rw [← Real.exp_nat_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A strengthened claim by induction, step by `calc` + `gcongr` (R1, R5, R6, R8) -/
example (u : ℕ → ℝ) (hu : ∀ n, u (n + 1) ≤ 3 * u n) (n : ℕ) :
    u n ≤ 3 ^ n * u 0 := by
  induction n with
    | zero => simp
    | succ k ih =>
      calc u (k + 1) ≤ 3 * u k := hu k
        _ ≤ 3 * (3 ^ k * u 0) := by gcongr
        _ = 3 ^ (k + 1) * u 0 := by rw [pow_succ]; ring

/-! ### W2. Replace a factor by a larger one, then cite an `exp` fact (R11, R13) -/
example (t s : ℝ) (hs : 0 ≤ s) : (1 + t) * s ≤ Real.exp t * s := by
  gcongr
  linarith [Real.add_one_le_exp t]

end M119Guide

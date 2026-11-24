/- Guide for M107 (Fixed-point iteration error).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other maps, other sequences).
Assumed: Lean basics.
-/
import Mathlib

open Filter Topology

namespace M107Guide

/-! # Part R · Reference entries -/

/-! ## Induction on the number of iterations -/

/-! ### R1. `induction n with | zero => … | succ n ih => …` · goal → two goals (`zero`, `succ`)
Each alternative must be finished after its `=>`. Mathlib's `induction' n with n ih` makes the same split
and leaves both goals open, so the second example shows them. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ m, P m → P (m + 1)) (n : ℕ) : P n := by
  induction n with
    | zero => exact h0
    | succ n ih => exact hs n ih

example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ m, P m → P (m + 1)) (n : ℕ) : P n := by
  induction' n with n ih
  · exact h0
  · exact hs n ih

/-! ### R2. `Function.iterate_zero_apply` · goal: `g^[0] y` → `y` -/
example {α : Type} (g : α → α) (y : α) (P : α → Prop) (h : P y) : P (g^[0] y) := by
  rw [Function.iterate_zero_apply]
  exact h

/-! ### R3. `pow_zero`, `one_mul` · goal: `c ^ 0 * a` → `1 * a` → `a` -/
example {M : Type} [Monoid M] (c a : M) (P : M → Prop) (h : P a) : P (c ^ 0 * a) := by
  rw [pow_zero]
  rw [one_mul]
  exact h

/-! ### R4. `Function.iterate_succ_apply'` · goal: `g^[n + 1] y` → `g (g^[n] y)` (peel the LAST step) -/
example {α : Type} (g : α → α) (n : ℕ) (y : α) (P : α → Prop) (h : P (g (g^[n] y))) :
    P (g^[n + 1] y) := by
  rw [Function.iterate_succ_apply']
  exact h

/-! ## Chaining estimates -/

/-! ### R5. `calc` · goal `a ≤ d` → one goal per step (`?_` leaves a step open) -/
example (a b c d : ℝ) (h1 : a = b) (h2 : b ≤ c) (h3 : c = d) : a ≤ d := by
  calc a = b := ?_
    _ ≤ c := ?_
    _ = d := ?_
  exacts [h1, h2, h3]

/-! ### R6. `hP _ _` · instantiate a `∀` hypothesis; Lean fills each `_` from the goal -/
example {α : Type} (Q : α → α → Prop) (hQ : ∀ x y, Q x y) (a b : α) : Q a b := by
  exact hQ _ _

/-! ### R7. `gcongr` · goal `c * a ≤ c * b` → `a ≤ b`; the side goal `0 ≤ c` is closed from the context -/
example (c a b d : ℝ) (hc : 0 ≤ c) (h1 : a ≤ d) (h2 : d ≤ b) : c * a ≤ c * b := by
  gcongr
  linarith

/-! ## The a posteriori bound -/

/-! ### R8. `set z := e` · context gains `z : τ := e`; every `e` in the goal becomes `z` -/
example (g : ℝ → ℝ) (n : ℕ) (y : ℝ) (P : ℝ → Prop) (h : ∀ w, P w) : P (g^[n] y + 1) := by
  set z := g^[n] y
  exact h _

/-! ### R9. `abs_sub_le` · `|a - c| ≤ |a - b| + |b - c|` (triangle inequality through `b`) · closes the goal
Typical use: a `calc` step `_ ≤ |a - b| + |b - c| := abs_sub_le _ _ _`, or `have t := abs_sub_le a b c`. -/
example (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  exact abs_sub_le a b c

/-! ### R10. `abs_sub_comm` · `|a - b| = |b - a|` · goal; `rw [abs_sub_comm a]` fixes which one -/
example (a b : ℝ) (P : ℝ → Prop) (h : P |b - a|) : P |a - b| := by
  rw [abs_sub_comm a]
  exact h

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

/-! ### R13. `linarith` · closes a goal that follows LINEARLY from the hypotheses -/
example (k : ℝ) (hk : k < 1) : 0 < 1 - k := by
  linarith

/-! ### R14. `nlinarith` · like `linarith`, but also multiplies pairs of hypotheses -/
example (k u v : ℝ) (hk : 0 ≤ k) (huv : u ≤ v) : k * u ≤ k * v := by
  nlinarith

/-! ## Limits -/

/-! ### R15. `tendsto_pow_atTop_nhds_zero_of_lt_one` · `0 ≤ r → r < 1 → rⁿ → 0` · context -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (G : Prop)
    (h : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) → G) : G := by
  have t := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  exact h t

/-! ### R16. `Filter.Tendsto.mul_const` · `uₙ → a` gives `uₙ * b → a * b` · context -/
example (u : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (G : Prop)
    (h : Tendsto (fun n => u n * b) atTop (𝓝 (a * b)) → G) : G := by
  have t := hu.mul_const b
  exact h t

/-! ### R17. `simpa using t` · simplifies `t` and the goal the same way (`0 * b` → `0`), then closes -/
example (u : ℕ → ℝ) (b : ℝ) (t : Tendsto (fun n => u n * b) atTop (𝓝 (0 * b))) :
    Tendsto (fun n => u n * b) atTop (𝓝 0) := by
  simpa using t

/-! ### R18. `tendsto_iff_norm_sub_tendsto_zero` · goal `uₙ → L` → `‖uₙ - L‖ → 0` -/
example (u : ℕ → ℝ) (L : ℝ) (h : Tendsto (fun n => ‖u n - L‖) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h

/-! ### R19. `squeeze_zero` · goal `gₙ → 0` → `gₙ ≤ uₙ` for one `n`, given `0 ≤ gₙ` and `uₙ → 0`
Arguments: `(∀ t, 0 ≤ g t)`, `(∀ t, g t ≤ u t)`, `Tendsto u l (𝓝 0)`. `fun t => ?_` leaves one bound open. -/
example (g u : ℕ → ℝ) (hg : ∀ t, 0 ≤ g t) (hgu : ∀ t, g t ≤ u t) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto g atTop (𝓝 0) := by
  refine squeeze_zero (fun t => hg t) (fun t => ?_) hu
  exact hgu t

/-! ### R20. `norm_nonneg` · `0 ≤ ‖a‖` · closes the goal -/
example (a : ℝ) : 0 ≤ ‖a‖ := by
  exact norm_nonneg _

/-! ### R21. `Real.norm_eq_abs` · goal: `‖r‖` → `|r|` (on `ℝ` the norm is the absolute value) -/
example (r : ℝ) (P : ℝ → Prop) (h : P |r|) : P ‖r‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A fixed point `hq : g q = q` used backwards: `rw [hq]` turns `g q` into `q`, then `rfl` closes -/
example (g : ℝ → ℝ) (q y : ℝ) (hq : g q = q) : |g y - q| = |g y - g q| := by
  rw [hq]

/-! ### W2. Induction on iterates of the doubling map: R1, R2, R3, R4, then `ring` -/
example (y : ℝ) (n : ℕ) : (fun x : ℝ => 2 * x)^[n] y = 2 ^ n * y := by
  induction n with
    | zero =>
      rw [Function.iterate_zero_apply, pow_zero, one_mul]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ring

/-! ### W3. A limit by squeezing: `(1/2)ⁿ / (n + 1) → 0` with R15, R19
`positivity` proves goals `0 ≤ e` / `0 < e` for expressions built from positive pieces.
`div_le_self : 0 ≤ a → 1 ≤ b → a / b ≤ a` gives the bound (`1 ≤ ↑n + 1` by `linarith`). -/
example : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n / (n + 1)) atTop (𝓝 0) := by
  have t := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) t
  exact div_le_self (by positivity) (by linarith)

/-! ### W4. A constant factor and `simpa`: `c · (1/3)ⁿ → 0` with R15, R16, R17 -/
example (c : ℝ) : Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n * c) atTop (𝓝 0) := by
  have t := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
  have t2 := t.mul_const c
  simpa using t2

end M107Guide

/- Guide for M125 (Gauss and Chebyshev nodes).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the midpoint rule on [0, 2],
other casts and denominators).
Assumed: Lean basics.
-/
import Mathlib

namespace M125Guide

/-! # Part R · Reference entries -/

/-! ## Moment equations from an exactness hypothesis -/

/-! ### R1. `have h := hk a (by norm_num)` · context gains `h : P a`
`∀ k ≤ 3, P k` is `∀ k, k ≤ 3 → P k`: apply it to a number, then prove `a ≤ 3` with `by norm_num`. -/
example (P : ℕ → Prop) (hk : ∀ k ≤ 3, P k) : P 2 := by
  have h := hk 2 (by norm_num)
  exact h

/-! ### R2. `integral_pow` · `∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)` · goal -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P ((b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1))) :
    P (∫ x in a..b, x ^ n) := by
  rw [integral_pow]
  exact h

/-! ### R3. `norm_num [integral_pow] at h` · context: the integral in `h` becomes a number
`norm_num` also cleans the left side: `x ^ 1` → `x`, `x ^ 0` → `1`, `w * 1` → `w`. -/
example (w x : ℝ) (h : w * x ^ 1 = ∫ t in (0:ℝ)..3, t ^ 1) : w * x = 9 / 2 := by
  norm_num [integral_pow] at h
  exact h

/-! ## Solving the moment equations -/

/-! ### R4. `linear_combination e` · closes `lhs = rhs` when `lhs - rhs` equals `e.lhs - e.rhs` by `ring`
`e` is a sum of hypotheses `hᵢ : aᵢ = bᵢ` with coefficients that may be polynomials (`x * h₁`). -/
example (a b x : ℝ) (h₁ : a + b = 2) (h₂ : a * x + b * x = 6) : x = 3 := by
  linear_combination (h₂ - x * h₁) / 2

/-! ### R5. `rintro rfl` · goal `x ≠ 0` → `False`; context: `x` replaced by `0` everywhere
`x ≠ 0` means `x = 0 → False`; the pattern `rfl` substitutes the equation instead of naming it. -/
example (x y : ℝ) (h : x * y = 1) (hf : (0 : ℝ) * y = 1 → False) : x ≠ 0 := by
  rintro rfl
  exact hf h

/-! ### R6. `norm_num at h` · closes the goal when `h` simplifies to `False` -/
example (y : ℝ) (h : 0 * y = -1 / 3) : False := by
  norm_num at h

/-! ### R7. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp` uses it left to right · context -/
example (a b : ℝ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have h' := mul_eq_zero.mp h
  exact h'

/-! ### R8. `Or.resolve_right` · `a ∨ b → ¬b → a` · context: drop the impossible side -/
example (A B : Prop) (h : A ∨ B) (hb : ¬B) : A := by
  have h' := h.resolve_right hb
  exact h'

/-! ### R9. `sub_eq_zero` · `a - b = 0 ↔ a = b`; `.mp` uses it left to right · context -/
example (a b : ℝ) (h : a - b = 0) : a = b := by
  have h' := sub_eq_zero.mp h
  exact h'

/-! ### R10. `linarith` · closes a goal that follows linearly from the hypotheses (`=`, `≤`, `<`) -/
example (a b : ℝ) (h₁ : a + b = 2) (h₂ : a = b) : a = 1 := by
  linarith

/-! ## Square roots and inline rewrites -/

/-! ### R11. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · context: `have hs := Real.sq_sqrt hx` -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (hp : P x) : P (√x ^ 2) := by
  have hs : √x ^ 2 = x := Real.sq_sqrt hx
  rw [hs]
  exact hp

/-! ### R12. `rw [show a = b by ring]` · goal: rewrite with an equation proved on the spot -/
example (s : ℝ) (P : ℝ → Prop) (h : P (1 / (s ^ 2) ^ 2)) : P ((1 / s) ^ 4) := by
  rw [show (1 / s) ^ 4 = 1 / (s ^ 2) ^ 2 by ring]
  exact h

/-! ## Chebyshev polynomials and the zeros of cosine -/

/-! ### R13. `Polynomial.Chebyshev.T_real_cos` · `(T ℝ n).eval (cos θ) = cos (n * θ)` (`n : ℤ`) · goal
With `m : ℕ`, `T ℝ m` is `T ℝ ↑m` (a cast `ℕ → ℤ`), so the result shows `↑↑m` (`ℕ → ℤ → ℝ`). -/
example (θ : ℝ) (m : ℕ) (P : ℝ → Prop) (h : P (Real.cos (((m : ℤ) : ℝ) * θ))) :
    P ((Polynomial.Chebyshev.T ℝ m).eval (Real.cos θ)) := by
  rw [Polynomial.Chebyshev.T_real_cos]
  exact h

/-! ### R14. `Real.cos_eq_zero_iff` · `cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * ↑k + 1) * π / 2` · goal -/
example (θ : ℝ) (h : ∃ k : ℤ, θ = (2 * k + 1) * Real.pi / 2) : Real.cos θ = 0 := by
  rw [Real.cos_eq_zero_iff]
  exact h

/-! ### R15. `refine ⟨k, ?_⟩` with `k : ℕ` for `∃ j : ℤ` · goal: the witness is cast, `↑k` -/
example (k : ℕ) (P : ℤ → Prop) (h : P ↑k) : ∃ j : ℤ, P j := by
  refine ⟨k, ?_⟩
  exact h

/-! ### R16. `push_cast` · goal: `↑↑k` (`ℕ → ℤ → ℝ`) → `↑k` (`ℕ → ℝ`), via `Int.cast_natCast` -/
example (k : ℕ) (P : ℝ → Prop) (h : P (k : ℝ)) : P (((k : ℤ) : ℝ)) := by
  push_cast
  exact h

/-! ### R17. `omega` · closes linear goals over `ℕ` and `ℤ` from the hypotheses -/
example (k n : ℕ) (hk : k < n) : 0 < n := by
  omega

/-! ### R18. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0`; uses hypotheses like `h : 0 < n` -/
example (n : ℕ) (h : 0 < n) : (2 * (n : ℝ)) ≠ 0 := by
  positivity

/-! ### R19. `field_simp` · goal: multiplies out the denominators it can prove `≠ 0` (from the
context) and closes the goal when what is left is a ring identity -/
example (x y : ℝ) (hx : x ≠ 0) : x * (y / (3 * x)) = y / 3 := by
  field_simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A one-point rule `w f(x)` exact for `1, x` on `[0, 2]` is the midpoint rule: R1, R3, R4 -/
example (w x : ℝ) (hexact : ∀ k ≤ 1, w * x ^ k = ∫ t in (0:ℝ)..2, t ^ k) : w = 2 ∧ x = 1 := by
  have h0 := hexact 0 (by norm_num)
  have h1 := hexact 1 (by norm_num)
  norm_num [integral_pow] at h0 h1
  refine ⟨h0, ?_⟩
  linear_combination (h1 - x * h0) / 2

/-! ### W2. The midpoint rule is not exact for `x²`: R2, then `norm_num` closes the `≠` -/
example : ∫ t in (0:ℝ)..2, t ^ 2 ≠ 2 * 1 ^ 2 := by
  rw [integral_pow]
  norm_num

/-! ### W3. A cast chain and a squared denominator: R18 for the `≠ 0` fact, then R16, R19 -/
example (m : ℕ) (h : 0 < m) (x : ℝ) : ((m : ℤ) : ℝ) * (x / (m : ℝ) ^ 2) = x / m := by
  have hm : (m : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end M125Guide

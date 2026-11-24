/- Guide for M117 (An unstable recurrence).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`x ^ 3`, `e^(x-2)`, `∫ x eˣ`,
the recurrence `aₙ₊₁ = 2aₙ + 1`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M117Guide

/-- An integral family used only in this guide: `F k = ∫₀¹ xᵏ dx`. -/
noncomputable def F (k : ℕ) : ℝ := ∫ x in (0:ℝ)..1, x ^ k

/-! # Part R · Reference entries -/

/-! ## Derivatives, one point at a time -/

/-! ### R1. `intro x hx` on `∀ x ∈ s, Q x` · context gains `x` and `hx : x ∈ s`; goal `Q x`
The term form `fun x hx => …` (or `fun x _ => …` when `hx` is not needed) does the same. -/
example (s : Set ℝ) (Q : ℝ → Prop) (h : ∀ x, Q x) : ∀ x ∈ s, Q x := by
  intro x hx
  exact h x

/-! ### R2. `hasDerivAt_pow` · `HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x` · context -/
example (n : ℕ) (x : ℝ) (G : Prop) (g : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x → G) :
    G := by
  have hd := hasDerivAt_pow n x
  exact g hd

/-! ### R3. `simpa using e` · simplifies `e` and the goal the same way, then closes the goal with `e`
Here `simp` turns `k + 1 - 1` into `k` and the cast `↑(k + 1)` into `↑k + 1`. -/
example (k : ℕ) (Q : ℝ → ℕ → Prop) (e : Q ↑(k + 1) (k + 1 - 1)) : Q (↑k + 1) k := by
  simpa using e

/-! ### R4. `hasDerivAt_id'` · `HasDerivAt (fun x => x) 1 x` · context -/
example (x : ℝ) (G : Prop) (g : HasDerivAt (fun x : ℝ => x) 1 x → G) : G := by
  have hd := hasDerivAt_id' x
  exact g hd

/-! ### R5. `HasDerivAt.sub_const` · `h.sub_const c : HasDerivAt (fun x => f x - c) f' x` · context
`h.sub_const c` is dot notation for `HasDerivAt.sub_const h c`. -/
example (f : ℝ → ℝ) (f' x c : ℝ) (h : HasDerivAt f f' x) (G : Prop)
    (g : HasDerivAt (fun x => f x - c) f' x → G) : G := by
  have h2 := h.sub_const c
  exact g h2

/-! ### R6. `HasDerivAt.exp` · chain rule for `Real.exp`: `h.exp` · context -/
example (f : ℝ → ℝ) (f' x : ℝ) (h : HasDerivAt f f' x) (G : Prop)
    (g : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x → G) : G := by
  have h2 := h.exp
  exact g h2

/-! ### R7. `HasDerivAt.congr_deriv` · goal `HasDerivAt f g' x` → `f' = g'` (fix the derivative's form) -/
example (f : ℝ → ℝ) (f' g' x : ℝ) (h : HasDerivAt f f' x) (e : f' = g') : HasDerivAt f g' x := by
  refine h.congr_deriv ?_
  exact e

/-! ## Integrability and integration by parts -/

/-! ### R8. `Continuous.intervalIntegrable` · goal: integrable on `[a, b]` → continuous -/
example (f : ℝ → ℝ) (a b : ℝ) (hf : Continuous f) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact hf

/-! ### R9. `fun_prop` · closes `Continuous f` when `f` is built from continuous pieces -/
example (c : ℝ) (k : ℕ) : Continuous fun x : ℝ => c * x ^ k * Real.exp (x + c) := by fun_prop

/-! ### R10. `intervalIntegral.integral_mul_deriv_eq_deriv_mul` · integration by parts · goal
`∫ₐᵇ u v' = u b · v b - u a · v a - ∫ₐᵇ u' v`, from derivatives on `[a, b]` and integrable `u'`, `v'`. -/
example (u v u' v' : ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' MeasureTheory.volume a b)
    (hv' : IntervalIntegrable v' MeasureTheory.volume a b) (P : ℝ → Prop)
    (h : P (u b * v b - u a * v a - ∫ x in a..b, u' x * v x)) :
    P (∫ x in a..b, u x * v' x) := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  exact h

/-! ### R11. `unfold d` · goal: the defined name `d` → its body -/
example (k : ℕ) (P : ℝ → Prop) (h : P (∫ x in (0:ℝ)..1, x ^ k)) : P (F k) := by
  unfold F
  exact h

/-! ## Boundary values -/

/-! ### R12. `sub_self`, then `Real.exp_zero` · goal: `Real.exp (a - a)` → `Real.exp 0` → `1` -/
example (a : ℝ) (P : ℝ → Prop) (h : P 1) : P (Real.exp (a - a)) := by
  rw [sub_self]
  rw [Real.exp_zero]
  exact h

/-! ### R13. `zero_pow` · `n ≠ 0 → 0 ^ n = 0` · goal rewritten, plus side goal `n ≠ 0` -/
example (k : ℕ) (P : ℝ → Prop) (h : P 0) : P ((0 : ℝ) ^ (k + 1)) := by
  rw [zero_pow]
  exact h
  simp

/-! ### R14. `one_pow`, `mul_one`, `zero_mul`, `sub_zero` · goal: the clean-up after R12, R13 -/
example (k : ℕ) (b c : ℝ) (P : ℝ → Prop) (h : P b) : P (1 ^ k * b - 0 * c) := by
  simp only [one_pow, one_mul, zero_mul, sub_zero]
  exact h

/-! ## Pulling a constant out of an integral -/

/-! ### R15. `funext x` · goal `f = g` (functions) → `f x = g x` for a new `x` -/
example (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-! ### R16. `rw [show A = B by tac]` · goal: rewrite with a fact proved on the spot
`rw [mul_assoc]` cannot reach inside `fun x => …`, so state the equation of the whole function. -/
example (c : ℝ) (f g : ℝ → ℝ) (P : (ℝ → ℝ) → Prop) (h : P fun x => c * (f x * g x)) :
    P fun x => c * f x * g x := by
  rw [show (fun x => c * f x * g x) = fun x => c * (f x * g x) by funext x; ring]
  exact h

/-! ### R17. `intervalIntegral.integral_const_mul` · `∫ x in a..b, c * f x = c * ∫ x in a..b, f x` · goal -/
example (c a b : ℝ) (f : ℝ → ℝ) (P : ℝ → Prop) (h : P (c * ∫ x in a..b, f x)) :
    P (∫ x in a..b, c * f x) := by
  rw [intervalIntegral.integral_const_mul]
  exact h

/-! ### R18. `push_cast` · goal: casts `↑(…)` of `+`, `*`, `1` pushed down to the variables -/
example (k m : ℕ) (P : ℝ → Prop) (h : P ((↑k + 1) * ↑m)) : P (↑((k + 1) * m)) := by
  push_cast
  exact h

/-! ## Induction on the recurrence -/

/-! ### R19. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: `P n` → `P 0` and `P (n + 1)` -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ### R20. `pow_zero`, `Nat.factorial_zero`, `Nat.cast_one`, `one_mul` · goal: the `n = 0` factors -/
example (c : ℝ) (P : ℝ → Prop) (h : P c) : P ((-1) ^ 0 * ↑(Nat.factorial 0) * c) := by
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  exact h

/-! ### R21. `rw [hs]` with `hs : ∀ n, a (n + 1) = g n (a n)` · goal: one step of a recurrence
`rw` finds the `n` itself. A theorem stated `∀ n` is used the same way. -/
example (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (hs : ∀ n, a (n + 1) = g n (a n)) (k : ℕ) (P : ℝ → Prop)
    (h : P (g k (a k))) : P (a (k + 1)) := by
  rw [hs]
  exact h

/-! ### R22. `Nat.factorial_succ` · `(n + 1)! = (n + 1) * n !` · goal -/
example (k : ℕ) (P : ℕ → Prop) (h : P ((k + 1) * k.factorial)) : P (k + 1).factorial := by
  rw [Nat.factorial_succ]
  exact h

/-! ### R23. `linear_combination e * ih` · closes a goal that is `e` times the equation `ih`, up to `ring` -/
example (a b c : ℝ) (ih : a = b) : 1 - c * a = 1 - c * b := by
  linear_combination (-c) * ih

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A power on an interval: R1, R2, R3 -/
example : ∀ x ∈ Set.uIcc (0:ℝ) 2, HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x :=
  fun x _ => by simpa using hasDerivAt_pow 3 x

/-! ### W2. `e^(x-2)` by dot notation: R4 → R5 → R6, then R7 with `ring` -/
example (x : ℝ) : HasDerivAt (fun x => Real.exp (x - 2)) (Real.exp (x - 2)) x :=
  ((hasDerivAt_id' x).sub_const 2).exp.congr_deriv (by ring)

/-! ### W3. Integration by parts on `∫₀¹ x eˣ dx` (u = x, v = eˣ): R1, R4, R6, R7, R8, R9, R10 -/
example : ∫ x in (0:ℝ)..1, x * Real.exp x = Real.exp 1 - ∫ x in (0:ℝ)..1, Real.exp x := by
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => x) 1 x := fun x _ => hasDerivAt_id' x
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => Real.exp x) (Real.exp x) x :=
    fun x _ => (hasDerivAt_id' x).exp.congr_deriv (by ring)
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    ((by fun_prop : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ => Real.exp x).intervalIntegrable _ _)]
  simp

/-! ### W4. Error propagation in `aₙ₊₁ = 2aₙ + 1`: R19, R21, R23 -/
example (a b : ℕ → ℝ) (ha : ∀ n, a (n + 1) = 2 * a n + 1) (hb : ∀ n, b (n + 1) = 2 * b n + 1)
    (n : ℕ) : a n - b n = 2 ^ n * (a 0 - b 0) := by
  induction n with | zero => ?_ | succ n ih => ?_
  · simp
  · rw [ha, hb]
    linear_combination 2 * ih

end M117Guide

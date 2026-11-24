/- Guide for H068 (Trapezoid rule error).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `k`) in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other functions, other integrals).
Infoview: `∫ (x : ℝ) in a..b, g x` is the interval integral `intervalIntegral g a b volume`;
`MeasureTheory.volume` is Lebesgue measure; `uIcc a b` is `[min a b, max a b]`; `Icc a b` is `[a, b]`;
`f - g`, `f * g`, `f ^ n`, `-f` on functions are pointwise; `↑3` is the natural number `3` cast into `ℝ`.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Set intervalIntegral

namespace H068Guide

/-! # Part R · Reference entries -/

/-! ## Continuity from a derivative (Part 1, MILESTONE `peano`) -/

/-! ### R1. `continuous_iff_continuousAt` · `Continuous g ↔ ∀ x, ContinuousAt g x` · goal -/
example (g : ℝ → ℝ) (h : ∀ x, ContinuousAt g x) : Continuous g := by
  rw [continuous_iff_continuousAt]
  exact h

/-! ### R2. `HasDerivAt.continuousAt` · `HasDerivAt g d x → ContinuousAt g x` · context gains `ContinuousAt g x`
Term form used with R1: `continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt`. -/
example (g : ℝ → ℝ) (d x : ℝ) (hg : HasDerivAt g d x) (G : Prop) (k : ContinuousAt g x → G) : G := by
  have hc := hg.continuousAt
  exact k hc

/-! ## Building a derivative, one operation at a time (Part 1 and Part 2)
`HasDerivAt u d x` says: `u` is differentiable at `x` with derivative `d` (a number, not a function).
Each lemma below turns derivative facts about the pieces into one about the combination. -/

/-! ### R3. `hasDerivAt_id'` · context gains `HasDerivAt (fun x => x) 1 x` (the identity) -/
example (x : ℝ) (G : Prop) (k : HasDerivAt (fun y : ℝ => y) 1 x → G) : G := by
  have h := hasDerivAt_id' x
  exact k h

/-! ### R4. `hasDerivAt_const` · context gains `HasDerivAt (fun x => c) 0 x` (a constant) -/
example (x c : ℝ) (G : Prop) (k : HasDerivAt (fun _ : ℝ => c) 0 x → G) : G := by
  have h := hasDerivAt_const x c
  exact k h

/-! ### R5. `HasDerivAt.sub_const` · `HasDerivAt u d x → HasDerivAt (fun x => u x - c) d x` · context -/
example (u : ℝ → ℝ) (d x c : ℝ) (hu : HasDerivAt u d x) (G : Prop)
    (k : HasDerivAt (fun y => u y - c) d x → G) : G := by
  have h := hu.sub_const c
  exact k h

/-! ### R6. `HasDerivAt.sub`, `HasDerivAt.add` · `HasDerivAt (u - v) (d - e) x`, `HasDerivAt (u + v) (d + e) x` · context
The function is printed as a pointwise difference `u - v` of functions, not as `fun x => u x - v x`. -/
example (u v : ℝ → ℝ) (d e x : ℝ) (hu : HasDerivAt u d x) (hv : HasDerivAt v e x) (G : Prop)
    (k : HasDerivAt (u - v) (d - e) x → HasDerivAt (u + v) (d + e) x → G) : G := by
  have h₁ := hu.sub hv
  have h₂ := hu.add hv
  exact k h₁ h₂

/-! ### R7. `HasDerivAt.mul` (product rule) · `HasDerivAt (u * v) (d * v x + u x * e) x` · context -/
example (u v : ℝ → ℝ) (d e x : ℝ) (hu : HasDerivAt u d x) (hv : HasDerivAt v e x) (G : Prop)
    (k : HasDerivAt (u * v) (d * v x + u x * e) x → G) : G := by
  have h := hu.mul hv
  exact k h

/-! ### R8. `HasDerivAt.const_mul` · `HasDerivAt (fun y => c * u y) (c * d) x` · context -/
example (u : ℝ → ℝ) (d x c : ℝ) (hu : HasDerivAt u d x) (G : Prop)
    (k : HasDerivAt (fun y => c * u y) (c * d) x → G) : G := by
  have h := hu.const_mul c
  exact k h

/-! ### R9. `HasDerivAt.div_const` · `HasDerivAt (fun x => u x / c) (d / c) x` · context -/
example (u : ℝ → ℝ) (d x c : ℝ) (hu : HasDerivAt u d x) (G : Prop)
    (k : HasDerivAt (fun y => u y / c) (d / c) x → G) : G := by
  have h := hu.div_const c
  exact k h

/-! ### R10. `HasDerivAt.congr_deriv` · `HasDerivAt u d x → d = e → HasDerivAt u e x` · goal → `d = e`
The function in `hu` only has to agree with the goal's function after unfolding (`fun x => u x - c`
and `(fun x => x) - fun x => c` both fit `fun x => x - c`); the derivative must be fixed by an equation. -/
example (u : ℝ → ℝ) (d e x : ℝ) (hu : HasDerivAt u d x) (h : d = e) : HasDerivAt u e x := by
  refine hu.congr_deriv ?_
  exact h

/-! ### R11. `Pi.sub_apply` · `(u - v) x = u x - v x` · goal: `simp only [Pi.sub_apply]` also beta-reduces
`(fun x => c) t` to `c`. This is what the derivative from R6 needs before `ring` can read it. -/
example (c t : ℝ) (P : ℝ → Prop) (h : P (c - t)) : P (((fun _ : ℝ => c) - fun y : ℝ => y) t) := by
  simp only [Pi.sub_apply]
  exact h

/-! ## Integration by parts and integrability (Part 1) -/

/-! ### R12. `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (integration by parts) · goal
`∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x`, given `HasDerivAt` for `u`, `v`
on `uIcc a b` and interval integrability of `u'`, `v'`. -/
example (u v u' v' : ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) (hv : ∀ x ∈ uIcc a b, HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' MeasureTheory.volume a b)
    (hv' : IntervalIntegrable v' MeasureTheory.volume a b)
    (P : ℝ → Prop) (h : P (u b * v b - u a * v a - ∫ x in a..b, u' x * v x)) :
    P (∫ x in a..b, u x * v' x) := by
  rw [integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  exact h

/-! ### R13. `fun x _ => hq x` · closes `∀ x ∈ s, Q x` from `hq : ∀ x, Q x` (ignore the membership proof) -/
example (s : Set ℝ) (Q : ℝ → Prop) (hq : ∀ x, Q x) : ∀ x ∈ s, Q x := by
  exact fun x _ => hq x

/-! ### R14. `Continuous.intervalIntegrable` · `Continuous g → ∀ a b, IntervalIntegrable g volume a b` · closes -/
example (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) : IntervalIntegrable g MeasureTheory.volume a b := by
  exact hg.intervalIntegrable a b

/-! ### R15. `fun_prop` · closes `Continuous fun t => …` built from `+ - * /`, `|·|`, powers, constants and
functions whose continuity is a hypothesis. For integrability write
`(by fun_prop : Continuous fun t : ℝ => …).intervalIntegrable _ _` (R14). -/
example (c : ℝ) (g : ℝ → ℝ) (hg : Continuous g) : Continuous fun t => |c * g t - t ^ 2 / 3| := by
  fun_prop

/-! ### R16. `intervalIntegrable_const` · closes `IntervalIntegrable (fun x => c) volume a b` -/
example (c a b : ℝ) : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b := by
  exact intervalIntegrable_const

/-! ### R17. `neg_one_mul` · `-1 * a = -a` · goal (`simp only` also rewrites under `∫`) -/
example (g : ℝ → ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (∫ x in a..b, -g x)) :
    P (∫ x in a..b, -1 * g x) := by
  simp only [neg_one_mul]
  exact h

/-! ### R18. `intervalIntegral.integral_neg` · `∫ x in a..b, -g x = -∫ x in a..b, g x` · goal -/
example (g : ℝ → ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (-∫ x in a..b, g x)) :
    P (∫ x in a..b, -g x) := by
  rw [integral_neg]
  exact h

/-! ## Antiderivatives and the fundamental theorem (Part 2, MILESTONE `kernel_integral`) -/

/-! ### R19. `HasDerivAt.pow` · `HasDerivAt (u ^ n) (↑n * u x ^ (n - 1) * d) x` · context
`↑n` is `n : ℕ` cast into `ℝ`, and `n - 1` is subtraction in `ℕ`; R21 cleans both up for a numeral `n`. -/
example (u : ℝ → ℝ) (d x : ℝ) (n : ℕ) (hu : HasDerivAt u d x) (G : Prop)
    (k : HasDerivAt (u ^ n) (↑n * u x ^ (n - 1) * d) x → G) : G := by
  have h := hu.pow n
  exact k h

/-! ### R20. `HasDerivAt.neg` · `HasDerivAt (-u) (-d) x` · context -/
example (u : ℝ → ℝ) (d x : ℝ) (hu : HasDerivAt u d x) (G : Prop) (k : HasDerivAt (-u) (-d) x → G) : G := by
  have h := hu.neg
  exact k h

/-! ### R21. `push_cast` · goal: casts of numerals `↑4` → `4`, and numeral arithmetic in `ℕ` (`4 - 1` → `3`) -/
example (y : ℝ) (P : ℝ → Prop) (h : P (4 * y ^ 3)) : P ((4 : ℕ) * y ^ (4 - 1)) := by
  push_cast
  exact h

/-! ### R22. `intervalIntegral.integral_eq_sub_of_hasDerivAt` (fundamental theorem of calculus) · goal
`(∀ x ∈ uIcc a b, HasDerivAt F (g x) x) → IntervalIntegrable g volume a b → ∫ x in a..b, g x = F b - F a`. -/
example (F g : ℝ → ℝ) (a b : ℝ) (hF : ∀ x ∈ uIcc a b, HasDerivAt F (g x) x)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) (P : ℝ → Prop) (h : P (F b - F a)) :
    P (∫ x in a..b, g x) := by
  rw [integral_eq_sub_of_hasDerivAt hF hg]
  exact h

/-! ## Signs (Part 3, MILESTONE `kernel_nonneg`) -/

/-! ### R23. `obtain ⟨h₁, h₂⟩ := hx` on `hx : x ∈ Icc a b` · context: `x ∈ Icc a b` is `a ≤ x ∧ x ≤ b`
(`Set.mem_Icc`), so it destructs like an `∧`. -/
example (a b x : ℝ) (hx : x ∈ Icc a b) (G : Prop) (k : a ≤ x → x ≤ b → G) : G := by
  obtain ⟨h₁, h₂⟩ := hx
  exact k h₁ h₂

/-! ### R24. `mul_nonneg` · `0 ≤ p → 0 ≤ q → 0 ≤ p * q` · goal list: one goal → two -/
example (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ p * q := by
  apply mul_nonneg
  exacts [hp, hq]

/-! ### R25. `linarith` · closes a linear (in)equality that follows from linear hypotheses in context -/
example (a x : ℝ) (h₁ : a ≤ x) : 0 ≤ (x - a) / 2 := by
  linarith

/-! ## Bounding an integral (Part 4, the spec theorem) -/

/-! ### R26. `abs_neg` · `|-p| = |p|` · goal -/
example (p : ℝ) (P : ℝ → Prop) (h : P |p|) : P |-p| := by
  rw [abs_neg]
  exact h

/-! ### R27. `intervalIntegral.abs_integral_le_integral_abs` · `a ≤ b → |∫ g| ≤ ∫ |g|` · closes
In a `calc`, it is the proof of the step `|∫ x in a..b, g x| ≤ ∫ x in a..b, |g x|`. -/
example (g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) : |∫ x in a..b, g x| ≤ ∫ x in a..b, |g x| := by
  exact abs_integral_le_integral_abs hab

/-! ### R28. `intervalIntegral.integral_mono_on` · goal list: `∫ g ≤ ∫ k` → integrability of `g`, of `k`,
and the pointwise bound on `Icc a b` -/
example (g k : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hk : IntervalIntegrable k MeasureTheory.volume a b) (hgk : ∀ x ∈ Icc a b, g x ≤ k x) :
    ∫ x in a..b, g x ≤ ∫ x in a..b, k x := by
  apply integral_mono_on hab
  exacts [hg, hk, hgk]

/-! ### R29. `abs_mul` · `|p * q| = |p| * |q|` · goal -/
example (p q : ℝ) (P : ℝ → Prop) (h : P (|p| * |q|)) : P |p * q| := by
  rw [abs_mul]
  exact h

/-! ### R30. `abs_of_nonneg` · `0 ≤ p → |p| = p` · goal: `rw [abs_of_nonneg hp]` -/
example (p : ℝ) (hp : 0 ≤ p) (P : ℝ → Prop) (h : P p) : P |p| := by
  rw [abs_of_nonneg hp]
  exact h

/-! ### R31. `mul_comm` · `p * q = q * p` · goal: bare `rw [mul_comm]` swaps the FIRST product it meets
(the outermost on the left of `≤`); `rw [mul_comm p q]` picks one. -/
example (p q r : ℝ) (P : ℝ → ℝ → Prop) (h : P (q * p) (r * p)) : P (p * q) (r * p) := by
  rw [mul_comm]
  exact h

/-! ### R32. `mul_le_mul_of_nonneg_right` · `q ≤ r → 0 ≤ p → q * p ≤ r * p` · goal list: one goal → two -/
example (p q r : ℝ) (hqr : q ≤ r) (hp : 0 ≤ p) : q * p ≤ r * p := by
  apply mul_le_mul_of_nonneg_right
  exacts [hqr, hp]

/-! ### R33. `intervalIntegral.integral_const_mul` · `∫ x in a..b, c * g x = c * ∫ x in a..b, g x` · goal -/
example (c a b : ℝ) (g : ℝ → ℝ) (P : ℝ → Prop) (h : P (c * ∫ x in a..b, g x)) :
    P (∫ x in a..b, c * g x) := by
  rw [integral_const_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A derivative built from pieces, then fixed: R3, R4, R6, R7, R10, R11, `ring` -/
example (x : ℝ) : HasDerivAt (fun t => t * (1 - t)) (1 - 2 * x) x := by
  have hd := (hasDerivAt_id' x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply]
  ring

/-! ### W2. FTC with a power: `∫₀¹ t² = 1/3` from the antiderivative `t³/3`: R19, R9, R10, R21, R22 -/
example : ∫ t in (0 : ℝ)..1, t ^ 2 = 1 / 3 := by
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => t ^ 3 / 3) (t ^ 2) t := by
    intro t _
    have hd := ((hasDerivAt_id' t).pow 3).div_const 3
    refine hd.congr_deriv ?_
    push_cast
    ring
  rw [integral_eq_sub_of_hasDerivAt hF ((by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable _ _)]
  norm_num

/-! ### W3. One integration by parts with `u = id`: R12 with R13, R3, R16, R14, then R17-style clean-up -/
example (g g' : ℝ → ℝ) (a b : ℝ) (hg : ∀ x, HasDerivAt g (g' x) x) (hc : Continuous g') :
    ∫ x in a..b, x * g' x = b * g b - a * g a - ∫ x in a..b, g x := by
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hasDerivAt_id' x) (fun x _ => hg x)
    intervalIntegrable_const (hc.intervalIntegrable _ _)]
  simp only [one_mul]

/-! ### W4. A pointwise bound under the integral: R28, R15 + R14 (twice), R32 -/
example (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) (hab : a ≤ b) (h1 : ∀ x ∈ Icc a b, |g x| ≤ 1) :
    ∫ x in a..b, |g x| * x ^ 2 ≤ ∫ x in a..b, 1 * x ^ 2 := by
  apply integral_mono_on hab
  · exact (by fun_prop : Continuous fun x => |g x| * x ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ => 1 * x ^ 2).intervalIntegrable _ _
  · intro x hx
    exact mul_le_mul_of_nonneg_right (h1 x hx) (sq_nonneg x)

end H068Guide

/- Guide for M118 (Euler's method on y' = λy).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a doubling recursion, other bounds).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter

namespace M118Guide

/-- A recursion used only in this guide: `dbl x₀ 0 = x₀`, `dbl x₀ (n + 1) = dbl x₀ n + dbl x₀ n`. -/
def dbl (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => dbl x₀ n + dbl x₀ n

/-! # Part R · Reference entries -/

/-! ## A closed form for a recursion: induction and unfolding -/

/-! ### R1. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: `P n` → `P 0` and `P (n + 1)`, plus `ih` -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ### R2. `simp only [d]` on `d … 0` · goal: the base equation of a recursive `def` is applied -/
example (x₀ : ℝ) (P : ℝ → Prop) (h : P x₀) : P (dbl x₀ 0) := by
  simp only [dbl]
  exact h

/-! ### R3. `rw [d]` on `d … (n + 1)` · goal: one step of the recursion is unfolded -/
example (x₀ : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (dbl x₀ n + dbl x₀ n)) : P (dbl x₀ (n + 1)) := by
  rw [dbl]
  exact h

/-! ### R4. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ## Using a proved theorem; monotonicity -/

/-! ### R5. `rw [thm]` with `thm : ∀ n, f n = g n` · goal: `rw` picks the arguments itself -/
example (f g : ℕ → ℝ) (thm : ∀ n, f n = g n) (n : ℕ) (P : ℝ → Prop) (h : P (g n)) : P (f n) := by
  rw [thm]
  exact h

/-! ### R6. `gcongr` on `a * c ≤ b * c` · goal → `a ≤ b`; side goal `0 ≤ c` closed from the context -/
example (a c : ℝ) (f : ℝ → ℝ) (hf : ∀ x, x ≤ f x) (hc : 0 ≤ c) : a * c ≤ f a * c := by
  gcongr
  exact hf a

/-! ### R7. `calc` · goal `a ≤ c` proved as a chain `a ≤ b`, `b = c`, each step with its own proof -/
example (a b c : ℝ) (hab : a ≤ b) (hbc : b = c) : a ≤ c := by
  calc a ≤ b := hab
    _ = c := hbc

/-! ### R8. `gcongr` on `a ^ n ≤ b ^ n` · goal → `a ≤ b`; side goal `0 ≤ a` closed from the context -/
example (a : ℝ) (n : ℕ) (f : ℝ → ℝ) (hf : ∀ x, x ≤ f x) (ha : 0 ≤ a) : a ^ n ≤ f a ^ n := by
  gcongr
  exact hf a

/-! ## The exponential -/

/-! ### R9. `Real.add_one_le_exp` · `x + 1 ≤ Real.exp x` · context gains the fact -/
example (x : ℝ) (P : Prop) (k : x + 1 ≤ Real.exp x → P) : P := by
  have h := Real.add_one_le_exp x
  exact k h

/-! ### R10. `linarith [t]` · closes a linear (in)equality from the context plus the extra facts `t` -/
example (x y : ℝ) (f : ℝ → ℝ) (hf : ∀ z, z + 1 ≤ f z) (hxy : y ≤ x) : y + 1 ≤ f x := by
  linarith [hf x]

/-! ### R11. `Real.exp_nat_mul` · `Real.exp (↑n * x) = Real.exp x ^ n`; right to left: `rw [← Real.exp_nat_mul]` -/
example (x : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (Real.exp (↑n * x))) : P (Real.exp x ^ n) := by
  rw [← Real.exp_nat_mul]
  exact h

/-! ### R12. `ring_nf` · closes `f s = f t` when `s`, `t` are equal as ring expressions (it normalises inside `f`) -/
example (a b c : ℝ) (f : ℝ → ℝ) : f (a * (b * c)) = f (c * (b * a)) := by
  ring_nf

/-! ## Absolute values -/

/-! ### R13. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R14. `abs_pow` · `|a ^ n| = |a| ^ n` · goal -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (|a| ^ n)) : P |a ^ n| := by
  rw [abs_pow]
  exact h

/-! ### R15. `abs_le` · `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b` · goal: an absolute-value bound → two linear bounds -/
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : |a| ≤ b := by
  rw [abs_le]
  exact ⟨h1, h2⟩

/-! ### R16. `nlinarith` · closes goals that need products of hypotheses (`linarith` fails here) -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  nlinarith

/-! ### R17. `one_pow`, `one_mul` (`simp` applies both) · goal: `1 ^ n * a` → `a` -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P a) : P (1 ^ n * a) := by
  rw [one_pow, one_mul]
  exact h

/-! ### R18. `abs_of_neg` · `a < 0 → |a| = -a` · goal rewritten, plus side goal `a < 0`
Write `rw [abs_of_neg (by linarith)]` to close the side goal on the spot. -/
example (a : ℝ) (P : ℝ → Prop) (h : P (-a)) (ha : a < 0) : P |a| := by
  rw [abs_of_neg]
  exact h
  exact ha

/-! ## Limits: `Tendsto u atTop atTop` means `u n → ∞` -/

/-! ### R19. `simp_rw [l]` · goal: rewrites under `fun n => …`, where `rw` cannot reach -/
example (f g : ℕ → ℝ) (thm : ∀ n, f n = g n) (P : (ℕ → ℝ) → Prop) (h : P (fun n => |g n|)) :
    P (fun n => |f n|) := by
  simp_rw [thm]
  exact h

/-! ### R20. `tendsto_pow_atTop_atTop_of_one_lt` · `1 < r → Tendsto (fun n => r ^ n) atTop atTop` · goal → `1 < r` -/
example (r : ℝ) (hr : 1 < r) : Tendsto (fun n : ℕ => r ^ n) atTop atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  exact hr

/-! ### R21. `Filter.Tendsto.atTop_mul_const` · `0 < r → Tendsto f l atTop → Tendsto (fun x => f x * r) l atTop`
Goal: `u n * c → ∞` → `u n → ∞`, given `0 < c`. -/
example (u : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => u n * c) atTop atTop := by
  apply Filter.Tendsto.atTop_mul_const hc
  exact hu

/-! ### R22. `abs_pos` · `0 < |a| ↔ a ≠ 0`; `abs_pos.mpr` turns `a ≠ 0` into `0 < |a|` · goal -/
example (a : ℝ) (ha : a ≠ 0) : 0 < |a| := by
  apply abs_pos.mpr
  exact ha

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Closed form of `dbl` by induction: R1, R2, R3, `rw [ih]`, R4, `ring` -/
example (x₀ : ℝ) (n : ℕ) : dbl x₀ n = 2 ^ n * x₀ := by
  induction n with | zero => ?_ | succ n ih => ?_
  · simp [dbl]
  · rw [dbl, ih, pow_succ]
    ring

/-! ### W2. `x ↦ 1 + x/2` lies below `exp (x/2)`, raised to the n-th power: R7, R8, R10, R9, R11, R12 -/
example (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (1 + x / 2) ^ n ≤ Real.exp (n * x / 2) := by
  calc (1 + x / 2) ^ n ≤ Real.exp (x / 2) ^ n := by
        gcongr
        linarith [Real.add_one_le_exp (x / 2)]
    _ = Real.exp (n * x / 2) := by rw [← Real.exp_nat_mul]; ring_nf

/-! ### W3. A geometric sequence with ratio `-3` blows up in absolute value: R13, R14, R19, R20, R21, R22 -/
example (c : ℝ) (hc : c ≠ 0) : Tendsto (fun n : ℕ => |(-3 : ℝ) ^ n * c|) atTop atTop := by
  have h3 : 1 < |(-3 : ℝ)| := by
    rw [abs_of_neg (by norm_num)]
    norm_num
  simp_rw [abs_mul, abs_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt h3).atTop_mul_const (abs_pos.mpr hc)

end M118Guide

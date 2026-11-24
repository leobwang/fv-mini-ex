/- Guide for H066 (Central differences are second order).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a degree-1 expansion, the
average `(f(x+h) + f(x-h))/2`, another bound).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Set

namespace H066Guide

/-! # Part R · Reference entries -/

/-! ## Intervals: `uIcc` and `UniqueDiffOn` -/

/-! ### R1. `rcases hab.lt_or_gt with h | h` (lemma `Ne.lt_or_gt`) · goal list: one goal per case
`Ne.lt_or_gt : a ≠ b → a < b ∨ b < a`; `rcases` splits the `∨`, each goal gets its own `h`. -/
example (a b : ℝ) (P : Prop) (hab : a ≠ b) (h₁ : a < b → P) (h₂ : b < a → P) : P := by
  rcases hab.lt_or_gt with h | h
  exacts [h₁ h, h₂ h]

/-! ### R2. `Set.uIcc_of_le` · `a ≤ b → uIcc a b = Icc a b` · goal: `uIcc` → `Icc` -/
example (a b : ℝ) (hab : a ≤ b) (P : Set ℝ → Prop) (h : P (Icc a b)) : P (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact h

/-! ### R3. `Set.uIcc_of_ge` · `b ≤ a → uIcc a b = Icc b a` · goal: `uIcc` → `Icc`, endpoints swapped -/
example (a b : ℝ) (hba : b ≤ a) (P : Set ℝ → Prop) (h : P (Icc b a)) : P (uIcc a b) := by
  rw [uIcc_of_ge hba]
  exact h

/-! ### R4. `uniqueDiffOn_Icc` · `a < b → UniqueDiffOn ℝ (Icc a b)` · closes the goal -/
example (a b : ℝ) (hab : a < b) : UniqueDiffOn ℝ (Icc a b) := by
  exact uniqueDiffOn_Icc hab

/-! ## Proving `a ≠ b` -/

/-! ### R5. `intro e` on `a ≠ b` · context gains `e : a = b`; goal → `False`
`a ≠ b` is notation for `a = b → False`, so `intro` works on it. -/
example (a b : ℝ) (h : a = b → False) : a ≠ b := by
  intro e
  exact h e

/-! ### R6. `apply hc` with `hc : c ≠ 0` · goal `False` → `c = 0` -/
example (c : ℝ) (hc : c ≠ 0) (h : c = 0) : False := by
  apply hc
  exact h

/-! ### R7. `linarith` · closes a linear (in)equality that follows from the hypotheses
It also closes `t ≠ u` (it assumes `t = u` and derives a contradiction). -/
example (a b : ℝ) (e : a + b = a) : b = 0 := by
  linarith

example (c : ℝ) (hc : 0 < c) : -c ≠ 0 := by
  linarith

/-! ## Taylor's theorem with Lagrange remainder -/

/-! ### R8. `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf` · context
gains the point `ξ` and the expansion `hξ`; `-` drops `ξ ∈ uIoo a b`. -/
example (f : ℝ → ℝ) (n : ℕ) (a b : ℝ) (hne : a ≠ b) (hf : ContDiffOn ℝ (n + 1) f (uIcc a b))
    (P : Prop) (h : ∀ ξ, f b - taylorWithinEval f n (uIcc a b) a b
      = iteratedDeriv (n + 1) f ξ * (b - a) ^ (n + 1) / ↑(n + 1).factorial → P) : P := by
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf
  exact h ξ hξ

/-! ### R9. `ContDiff.contDiffOn` · `ContDiff ℝ n f → ContDiffOn ℝ n f s` · closes the goal -/
example (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (hf : ContDiff ℝ n f) : ContDiffOn ℝ n f s := by
  exact hf.contDiffOn

/-! ### R10. `taylorWithinEval_succ` · goal: peel the top term off a Taylor polynomial
`taylorWithinEval f (n+1) s a b = taylorWithinEval f n s a b + (coeff * (b - a)^(n+1)) • iteratedDerivWithin (n+1) f s a`.
On a numeral degree `2` it matches with `n := 1`, so the new term shows `1 + 1`.
`rw [taylorWithinEval_succ] at hξ` does the same to a hypothesis `hξ` instead of the goal. -/
example (f : ℝ → ℝ) (s : Set ℝ) (a b : ℝ) (P : ℝ → Prop)
    (h : P (taylorWithinEval f 1 s a b +
      (((((1 : ℕ) : ℝ) + 1) * ((Nat.factorial 1 : ℕ) : ℝ))⁻¹ * (b - a) ^ (1 + 1)) •
        iteratedDerivWithin (1 + 1) f s a)) :
    P (taylorWithinEval f 2 s a b) := by
  rw [taylorWithinEval_succ]
  exact h

/-! ### R11. `taylor_within_zero_eval` · `taylorWithinEval f 0 s a b = f a` · context (with `at hξ`) -/
example (f : ℝ → ℝ) (s : Set ℝ) (a b : ℝ) (P : ℝ → Prop)
    (hξ : P (taylorWithinEval f 0 s a b)) : P (f a) := by
  rw [taylor_within_zero_eval] at hξ
  exact hξ

/-! ## Coefficients: `iteratedDerivWithin` → `iteratedDeriv` -/

/-! ### R12. `iteratedDerivWithin_eq_iteratedDeriv` · goal: derivative within `s` → plain derivative
Needs `UniqueDiffOn ℝ s`, `ContDiffAt ℝ n f a` and `a ∈ s`. -/
example (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a : ℝ) (hs : UniqueDiffOn ℝ s)
    (hf : ContDiffAt ℝ n f a) (ha : a ∈ s) (P : ℝ → Prop) (h : P (iteratedDeriv n f a)) :
    P (iteratedDerivWithin n f s a) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv hs hf ha]
  exact h

/-! ### R13. `ContDiff.contDiffAt` · `ContDiff ℝ n f → ContDiffAt ℝ n f a` · closes the goal -/
example (f : ℝ → ℝ) (n : ℕ) (a : ℝ) (hf : ContDiff ℝ n f) : ContDiffAt ℝ n f a := by
  exact hf.contDiffAt

/-! ### R14. `ContDiffAt.of_le` · lower the order: goal `ContDiffAt ℝ m f a` → `↑m ≤ ↑n` -/
example (f : ℝ → ℝ) (m n : ℕ) (a : ℝ) (hf : ContDiffAt ℝ n f a) (hmn : (m : WithTop ℕ∞) ≤ n) :
    ContDiffAt ℝ m f a := by
  apply hf.of_le
  exact hmn

/-! ### R15. `norm_num` on an order `↑2 ≤ 3` in `WithTop ℕ∞` · closes the goal -/
example : ((2 : ℕ) : WithTop ℕ∞) ≤ 3 := by
  norm_num

/-! ### R16. `Set.left_mem_uIcc` · `a ∈ uIcc a b` · closes the goal -/
example (a b : ℝ) : a ∈ uIcc a b := by
  exact left_mem_uIcc

/-! ### R17. `iteratedDeriv_one` · `iteratedDeriv 1 f = deriv f` · goal -/
example (f : ℝ → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (deriv f a)) : P (iteratedDeriv 1 f a) := by
  rw [iteratedDeriv_one]
  exact h

/-! ## Cleaning up and closing an equation -/

/-! ### R18. `norm_num [Nat.factorial] at hξ` · context: casts, factorials, `•` and `a + c - a` evaluated
In `ℝ`, `r • d` is `r * d` (`smul_eq_mul`); `norm_num` applies it by itself. -/
example (a c d : ℝ) (P : ℝ → Prop)
    (hξ : P ((((((1 : ℕ) : ℝ) + 1) * ((Nat.factorial 1 : ℕ) : ℝ))⁻¹ * (a + c - a) ^ (1 + 1)) • d)) :
    P (1 / 2 * c ^ 2 * d) := by
  norm_num [Nat.factorial] at hξ
  exact hξ

/-! ### R19. `linear_combination hξ` · closes `lhs = rhs` when `lhs - rhs` is `hξ.lhs - hξ.rhs` up to `ring` -/
example (a b c d : ℝ) (hξ : a - (b + c) = d) : a = b + c + d := by
  linear_combination hξ

/-! ### R20. `sub_eq_add_neg` · `a - b = a + -b`; right to left: `rw [← sub_eq_add_neg] at h` · context -/
example (f : ℝ → ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (f (a + -b))) : P (f (a - b)) := by
  rw [← sub_eq_add_neg] at h
  exact h

/-! ### R21. `field_simp` · goal: clear the denominators (it needs to know they are `≠ 0`) -/
example (a b c : ℝ) (hc : 0 < c) (h : a = 2 * c * b) : a / (2 * c) = b := by
  field_simp
  exact h

/-! ## Absolute values and the final bound -/

/-! ### R22. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R23. `abs_of_pos` · `0 < a → |a| = a` · goal rewritten, plus side goal `0 < a` -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) (ha : 0 < a) : P |a| := by
  rw [abs_of_pos]
  exact h
  exact ha

/-! ### R24. `positivity` · closes `0 < e` / `0 ≤ e` built from `+ * / ^`, numerals and positive atoms -/
example (c : ℝ) (hc : 0 < c) : 0 < c ^ 2 / 7 := by
  positivity

/-! ### R25. `have h12 := abs_add_le a b` · context gains `|a + b| ≤ |a| + |b|` -/
example (a b : ℝ) (P : Prop) (h : |a + b| ≤ |a| + |b| → P) : P := by
  have h12 := abs_add_le a b
  exact h h12

/-! ### R26. `calc` · goal `a ≤ c` → a chain of steps `a ≤ b`, `b = c`, each with its own proof -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := by
  calc a ≤ b := h₁
    _ = c := h₂

/-! ### R27. `gcongr` · goal `c * a ≤ c * b` → `a ≤ b` (the side goal `0 ≤ c` is closed for you) -/
example (a b c d : ℝ) (hc : 0 < c) (h₁ : a ≤ d) (h₂ : d ≤ b) : c * a ≤ c * b := by
  gcongr
  exact h₁.trans h₂

/-! ### R28. `linarith [t₁, t₂]` · `linarith` with extra facts `tᵢ` added to the context first -/
example (g : ℝ → ℝ) (M a b : ℝ) (hM : ∀ y, g y ≤ M) : g a + g b ≤ M + M := by
  linarith [hM a, hM b]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A degree-1 expansion: R8, R9, R10, R11, R12–R17, R18, R19 -/
example (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (a b : ℝ) (hab : a < b) :
    ∃ ξ, f b = f a + (b - a) * deriv f a + iteratedDeriv 2 f ξ * (b - a) ^ 2 / 2 := by
  obtain ⟨ξ, -, hξ⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) (x₀ := a) (x := b) hab.ne hf.contDiffOn
  refine ⟨ξ, ?_⟩
  have hu : UniqueDiffOn ℝ (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact uniqueDiffOn_Icc hab
  have d1 : iteratedDerivWithin 1 f (uIcc a b) a = deriv f a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc,
      iteratedDeriv_one]
  rw [taylorWithinEval_succ, taylor_within_zero_eval, d1] at hξ
  norm_num [Nat.factorial] at hξ
  linear_combination hξ

/-! ### W2. Adding two expansions cancels the odd term: R20, R21, `ring` -/
example (f : ℝ → ℝ) (x c p q : ℝ)
    (h1 : f (x + c) = f x + c * p + c ^ 2 * q) (h2 : f (x + -c) = f x - c * p + c ^ 2 * q) :
    (f (x + c) + f (x - c)) / 2 - f x = c ^ 2 * q := by
  rw [← sub_eq_add_neg] at h2
  rw [h1, h2]
  field_simp
  ring

/-! ### W3. A bound through `|·|`: R22, R23 with R24, R25, R26, R27, R28 -/
example (g : ℝ → ℝ) (M c a b : ℝ) (hc : 0 < c) (hM : ∀ y, |g y| ≤ M) :
    |c / 3 * (g a + g b)| ≤ 2 * M * c / 3 := by
  rw [abs_mul, abs_of_pos (by positivity)]
  have h12 := abs_add_le (g a) (g b)
  calc c / 3 * |g a + g b| ≤ c / 3 * (M + M) := by
        gcongr
        linarith [hM a, hM b]
    _ = 2 * M * c / 3 := by ring

/-! ### W4. The ORDER trap: `norm_num` first turns a degree-1 coefficient into `derivWithin`,
which no longer matches `iteratedDerivWithin 1 f s a` (so the R12 rewrite fails afterwards) -/
example (f : ℝ → ℝ) (s : Set ℝ) (a : ℝ) (P : ℝ → Prop) (hξ : P (iteratedDerivWithin 1 f s a)) :
    P (derivWithin f s a) := by
  norm_num at hξ
  exact hξ

end H066Guide

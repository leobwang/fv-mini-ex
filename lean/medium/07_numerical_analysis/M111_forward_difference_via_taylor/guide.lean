/- Guide for M111 (Forward difference via Taylor).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (degree 2, the right endpoint,
other difference quotients and bounds).
Assumed: Lean basics.
-/
import Mathlib

namespace M111Guide

/-! # Part R · Reference entries -/

/-! ## Taylor's theorem with Lagrange remainder -/

/-! ### R1. `obtain ⟨y, -, hy⟩ := h` · context: `h : ∃ y ∈ S, Q y` → `y` and `hy : Q y`
`∃ y ∈ S, Q y` is `∃ y, y ∈ S ∧ Q y`; the `-` discards the membership. For `∃ y, Q y` write `⟨y, hy⟩`. -/
example {α : Type} (S : Set α) (Q : α → Prop) (G : Prop) (g : ∀ y, Q y → G)
    (h : ∃ y ∈ S, Q y) : G := by
  obtain ⟨y, -, hy⟩ := h
  exact g y hy

/-! ### R2. `taylor_mean_remainder_lagrange_iteratedDeriv` · context gains `ξ` and the remainder `hξ`
`a ≠ b → ContDiffOn ℝ (↑n + 1) f (Set.uIcc a b) → ∃ ξ ∈ Set.uIoo a b,
   f b - taylorWithinEval f n (Set.uIcc a b) a b = iteratedDeriv (n + 1) f ξ * (b - a) ^ (n + 1) / ↑(n + 1).factorial`.
In the lemma `x₀` is the expansion point and `x` the evaluation point: pass them as `(x₀ := a) (x := b)`. -/
example (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (hne : a ≠ b) (hf : ContDiffOn ℝ (↑n + 1) f (Set.uIcc a b))
    (G : Prop) (g : G) : G := by
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) (x₀ := a) (x := b) hne hf
  exact g

/-! ### R3. `ContDiff.contDiffOn` · closes `ContDiffOn ℝ k f s` from `hf : ContDiff ℝ k f`
`hf.contDiffOn` restricts "k times continuously differentiable everywhere" to any set `s`. -/
example (f : ℝ → ℝ) (k : WithTop ℕ∞) (s : Set ℝ) (hf : ContDiff ℝ k f) : ContDiffOn ℝ k f s := by
  exact hf.contDiffOn

/-! ### R4. `linarith` · closes a linear `<`, `≤`, `=` or `≠` goal from the hypotheses -/
example (a t : ℝ) (ht : 0 < t) : a ≠ a + t := by linarith

/-! ## The one Taylor coefficient: a derivative within an interval -/

/-! ### R5. `iteratedDerivWithin_one` · goal: `iteratedDerivWithin 1 f s` → `derivWithin f s` -/
example (f : ℝ → ℝ) (s : Set ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (derivWithin f s a)) :
    P (iteratedDerivWithin 1 f s a) := by
  rw [iteratedDerivWithin_one]
  exact h

/-! ### R6. `Set.uIcc_of_le` · `a ≤ b → Set.uIcc a b = Set.Icc a b` · goal rewritten, side goal `a ≤ b`
Write `rw [Set.uIcc_of_le (by linarith)]` to close the side goal on the spot. -/
example (a b : ℝ) (hab : a ≤ b) (P : Set ℝ → Prop) (h : P (Set.Icc a b)) : P (Set.uIcc a b) := by
  rw [Set.uIcc_of_le]
  exact h
  exact hab

/-! ### R7. `ContDiff.differentiable` · `ContDiff 𝕜 k f → k ≠ 0 → Differentiable 𝕜 f`
`apply` leaves the side goal `k ≠ 0` (here in `WithTop ℕ∞`); `norm_num` closes it. -/
example (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) : Differentiable ℝ f := by
  apply hf.differentiable
  norm_num

/-! ### R8. `DifferentiableAt.derivWithin` · goal `derivWithin f s x = deriv f x` → `UniqueDiffWithinAt ℝ s x` -/
example (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) (hd : DifferentiableAt ℝ f x)
    (hu : UniqueDiffWithinAt ℝ s x) : derivWithin f s x = deriv f x := by
  apply hd.derivWithin
  exact hu

/-! ### R9. `uniqueDiffOn_Icc` · `a < b → UniqueDiffOn ℝ (Set.Icc a b)` · goal: `UniqueDiffWithinAt` → membership
`UniqueDiffOn ℝ s` is `∀ x ∈ s, UniqueDiffWithinAt ℝ s x`, so `uniqueDiffOn_Icc hab x hx` is a term. -/
example (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) : UniqueDiffWithinAt ℝ (Set.Icc a b) x := by
  apply uniqueDiffOn_Icc hab
  exact hx

/-! ### R10. `⟨le_rfl, ?_⟩` · goal: `a ∈ Set.Icc a b` (that is `a ≤ a ∧ a ≤ b`) → `a ≤ b` -/
example (a b : ℝ) (hab : a ≤ b) : a ∈ Set.Icc a b := by
  refine ⟨le_rfl, ?_⟩
  exact hab

/-! ## Reading off the Taylor polynomial -/

/-! ### R11. `taylorWithinEval_succ` · goal: degree `n + 1` → degree `n` plus one more term -/
example (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a b : ℝ) (P : ℝ → Prop)
    (h : P (taylorWithinEval f n s a b +
      ((((n : ℝ) + 1) * (n.factorial : ℝ))⁻¹ * (b - a) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s a)) :
    P (taylorWithinEval f (n + 1) s a b) := by
  rw [taylorWithinEval_succ]
  exact h

/-! ### R12. `rw [taylor_within_zero_eval] at h` · context: degree 0 is the value `f a` -/
example (f : ℝ → ℝ) (s : Set ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (taylorWithinEval f 0 s a b)) :
    P (f a) := by
  rw [taylor_within_zero_eval] at h
  exact h

/-! ### R13. `norm_num at h` · context: the numerals in `h` are computed and `c • d` becomes `c * d` -/
example (a b d : ℝ) (P : ℝ → Prop)
    (h : P ((((((0 : ℕ) : ℝ) + 1) * ((Nat.factorial 0 : ℕ) : ℝ))⁻¹ * (a + b - a) ^ (0 + 1)) • d)) :
    P (b * d) := by
  norm_num at h
  exact h

/-! ## From the remainder to the bound -/

/-! ### R14. `field_simp` · goal: an equation with `/ b` → one without denominators
It needs `b ≠ 0`; it finds it from `hb : 0 < b` in the context. -/
example (a b c d : ℝ) (hb : 0 < b) (h : (a - b * c) * 3 = b * d) : a / b - c = d / 3 := by
  field_simp
  exact h

/-! ### R15. `linear_combination k * h` · closes `L = R` when `L - R = k * (lhs h - rhs h)` by `ring` -/
example (a b : ℝ) (h : a = 2 * b) : 3 * a = 6 * b := by linear_combination 3 * h

/-! ### R16. `abs_div` · `|a / b| = |a| / |b|` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R17. `abs_mul` · `|a * b| = |a| * |b|` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R18. `abs_of_pos` · `0 < a → |a| = a`: write `rw [abs_of_pos ha]` -/
example (a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ### R19. `abs_two` · `|2| = 2` -/
example (P : ℝ → Prop) (h : P 2) : P |(2 : ℝ)| := by
  rw [abs_two]
  exact h

/-! ### R20. `gcongr` · goal `u * c / d ≤ v * c / d` → `u ≤ v` (the common factors are matched off)
Side goals such as `0 ≤ c` are closed from hypotheses like `hc : 0 < c`. -/
example (g : ℝ → ℝ) (K c : ℝ) (y : ℝ) (hc : 0 < c) (hg : ∀ t, g t ≤ K) :
    g y * c / 2 ≤ K * c / 2 := by
  gcongr
  exact hg y

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The degree-2 Taylor polynomial read off: R11 twice, R12, then `norm_num`
`norm_num` also turns `iteratedDerivWithin 1` into `derivWithin` by itself. -/
example (f : ℝ → ℝ) (s : Set ℝ) (a b c : ℝ)
    (h : f a + (b - a) * derivWithin f s a + 1 / 2 * (b - a) ^ 2 * iteratedDerivWithin 2 f s a = c) :
    taylorWithinEval f 2 s a b = c := by
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
  norm_num
  exact h

/-! ### W2. A derivative within `[a, b]` at the RIGHT endpoint is the ordinary one: R7, R8, R9 -/
example (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (a b : ℝ) (hab : a < b) :
    derivWithin f (Set.Icc a b) b = deriv f b := by
  apply (hf.differentiable (by norm_num) b).derivWithin
  exact uniqueDiffOn_Icc hab b ⟨hab.le, le_rfl⟩

/-! ### W3. A difference quotient from an exact difference: R14, R15 -/
example (g : ℝ → ℝ) (t k : ℝ) (hk : 0 < k) (h : g (t + k) - g t = 3 * k + k ^ 2) :
    (g (t + k) - g t) / k - 3 = k := by
  field_simp
  linear_combination h

/-! ### W4. A bound through absolute values: R16, R17, R18, then `gcongr` (R20) -/
example (c K t : ℝ) (ht : 0 < t) (hc : |c| ≤ K) : |c * t / 3| ≤ K * t / 3 := by
  rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  gcongr

end M111Guide

/- Guide for H065 (Newton's method converges quadratically).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G` is "any goal" when the step changes only the context.
Part W: worked combinations on objects that are NOT the exercise's (degree-0 Taylor, a toy sequence,
another quotient).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Set

namespace H065Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Taylor's theorem of order 1 -/

/-! ### R1. `rcases eq_or_ne x y with rfl | hxy` · goal list: case `x = y` (substituted) and case `x ≠ y` -/
example {α : Type} (x y : α) (P : α → α → Prop) (h1 : ∀ a, P a a) (h2 : x ≠ y → P x y) :
    P x y := by
  rcases eq_or_ne x y with rfl | hxy
  · exact h1 x
  · exact h2 hxy

/-! ### R2. `sub_self` · `a - a = 0`; then `simp` clears `* 0`, `0 ^ 2`, `+ 0` -/
example (a b c d : ℝ) : c = c + a * (d - d) + b * (d - d) ^ 2 := by
  rw [sub_self]
  simp

/-! ### R3. `ContDiff.contDiffOn` · context gains `ContDiffOn 𝕜 n g s` (on any set `s`) -/
example (g : ℝ → ℝ) (s : Set ℝ) (hg : ContDiff ℝ 2 g) : ContDiffOn ℝ 2 g s := by
  have h := hg.contDiffOn (s := s)
  exact h

/-! ### R4. `taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)` · context gains `ξ` and the
Taylor identity with Lagrange remainder on `uIcc a b`; `-` drops the fact `ξ ∈ uIoo a b`. -/
example (g : ℝ → ℝ) (a b : ℝ) (hab : a ≠ b) (hg : ContDiffOn ℝ 2 g (uIcc a b)) (G : Prop)
    (hG : ∀ t : ℝ, t = t → G) : G := by
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hab hg
  exact hG ξ rfl

/-! ### R5. `rcases hab.lt_or_gt with h | h` (lemma `Ne.lt_or_gt`) · goal list: `a < b` and `b < a` -/
example (a b : ℝ) (hab : a ≠ b) (P : Prop) (h1 : a < b → P) (h2 : b < a → P) : P := by
  rcases hab.lt_or_gt with h | h
  · exact h1 h
  · exact h2 h

/-! ### R6. `Set.uIcc_of_le` · `a ≤ b → uIcc a b = Icc a b` · goal -/
example (a b : ℝ) (h : a < b) (P : Set ℝ → Prop) (hP : P (Icc a b)) : P (uIcc a b) := by
  rw [uIcc_of_le h.le]
  exact hP

/-! ### R7. `Set.uIcc_of_ge` · `b ≤ a → uIcc a b = Icc b a` · goal -/
example (a b : ℝ) (h : b < a) (P : Set ℝ → Prop) (hP : P (Icc b a)) : P (uIcc a b) := by
  rw [uIcc_of_ge h.le]
  exact hP

/-! ### R8. `uniqueDiffOn_Icc` · `a < b → UniqueDiffOn ℝ (Icc a b)` · closes the goal -/
example (a b : ℝ) (h : a < b) : UniqueDiffOn ℝ (Icc a b) := by
  exact uniqueDiffOn_Icc h

/-! ### R9. `ContDiff.contDiffAt`, `ContDiffAt.of_le` · goal `ContDiffAt ℝ 1 g a` → side goal `1 ≤ 2` -/
example (g : ℝ → ℝ) (a : ℝ) (hg : ContDiff ℝ 2 g) : ContDiffAt ℝ 1 g a := by
  apply ContDiffAt.of_le hg.contDiffAt
  norm_num

/-! ### R10. `Set.left_mem_uIcc` · `a ∈ uIcc a b` · closes the goal -/
example (a b : ℝ) : a ∈ uIcc a b := by
  exact left_mem_uIcc

/-! ### R11. `iteratedDerivWithin_eq_iteratedDeriv` · goal: the derivative within `s` → the plain one -/
example (g : ℝ → ℝ) (s : Set ℝ) (a : ℝ) (n : ℕ) (hs : UniqueDiffOn ℝ s) (hg : ContDiffAt ℝ n g a)
    (ha : a ∈ s) (P : ℝ → Prop) (h : P (iteratedDeriv n g a)) : P (iteratedDerivWithin n g s a) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv hs hg ha]
  exact h

/-! ### R12. `iteratedDeriv_one` · goal: `iteratedDeriv 1 g` → `deriv g` -/
example (g : ℝ → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (deriv g a)) : P (iteratedDeriv 1 g a) := by
  rw [iteratedDeriv_one]
  exact h

/-! ### R13. `rw [taylorWithinEval_succ] at h` · context: degree `n + 1` → degree `n` plus one term -/
example (g : ℝ → ℝ) (s : Set ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (taylorWithinEval g 1 s a b))
    (G : Prop) (hG : ∀ t, P t → G) : G := by
  rw [taylorWithinEval_succ] at h
  exact hG _ h

/-! ### R14. `rw [taylor_within_zero_eval] at h` · context: the degree-0 polynomial → `g a` -/
example (g : ℝ → ℝ) (s : Set ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (taylorWithinEval g 0 s a b))
    (G : Prop) (hG : ∀ t, P t → G) : G := by
  rw [taylor_within_zero_eval] at h
  exact hG _ h

/-! ### R15. `norm_num at h` · context: numerals in `h` evaluated (`↑(1 + 1).factorial` → `2`, `•` → `*`) -/
example (g : ℝ → ℝ) (t c e : ℝ)
    (h : (((((0 : ℕ) : ℝ) + 1) * ((Nat.factorial 0 : ℕ) : ℝ))⁻¹ * e ^ (0 + 1)) • c =
      iteratedDeriv (1 + 1) g t * e ^ (1 + 1) / (((1 + 1).factorial : ℕ) : ℝ))
    (G : Prop) (hG : ∀ u v : ℝ, u = v → G) : G := by
  norm_num at h
  exact hG _ _ h

/-! ### R16. `linear_combination k * h` · closes `L = R` when `L - R - k * (h.lhs - h.rhs)` is `0` by `ring` -/
example (a b c : ℝ) (h : a - b = c) : 2 * a = 2 * b + 2 * c := by
  linear_combination 2 * h

/-! ## Part 2 · The exact Newton error -/

/-! ### R17. `h₁.symm.trans h₂` (`Eq.symm`, `Eq.trans`) · context gains `b = c` from `a = b`, `a = c` -/
example {α : Type} (a b c : α) (h₁ : a = b) (h₂ : a = c) (G : Prop) (hG : b = c → G) : G := by
  have h := h₁.symm.trans h₂
  exact hG h

/-! ### R18. `unfold D` · goal: the defined name `D` → its body -/
noncomputable def halve (g : ℝ → ℝ) (x : ℝ) : ℝ := g x / 2
example (g : ℝ → ℝ) (x : ℝ) (P : ℝ → Prop) (h : P (g x / 2)) : P (halve g x) := by
  unfold halve
  exact h

/-! ### R19. `field_simp` · goal: denominators cleared, using the `≠ 0` facts in the context -/
example (a b c d : ℝ) (hb : b ≠ 0) (h : a * b - c = d * b) : a - c / b = d := by
  field_simp
  linear_combination h

/-! ## Part 3 · A bound is nonnegative -/

/-! ### R20. `abs_nonneg` · `0 ≤ |a|` · context gains it -/
example (a : ℝ) (G : Prop) (hG : 0 ≤ |a| → G) : G := by
  have h := abs_nonneg a
  exact hG h

/-! ### R21. `h₁.trans h₂`, `h₁.trans_le h₂` · chain `a ≤ b ≤ c` / `a < b ≤ c` · context gains the result -/
example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) (G : Prop) (hG : a < c → G) : G := by
  have h := h₁.trans_le h₂
  exact hG h

/-! ## Part 4 · One Newton step -/

/-! ### R22. `abs_pos` · `0 < |a| ↔ a ≠ 0`; `.mp` reads it left to right · context -/
example (a : ℝ) (ha : 0 < |a|) (G : Prop) (hG : a ≠ 0 → G) : G := by
  have h := abs_pos.mp ha
  exact hG h

/-! ### R23. `abs_div` · `|a / b| = |a| / |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R24. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R25. `abs_two` · `|2| = 2` · goal -/
example (P : ℝ → Prop) (h : P 2) : P |2| := by
  rw [abs_two]
  exact h

/-! ### R26. `abs_pow` · `|a ^ n| = |a| ^ n` · goal -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (|a| ^ n)) : P |a ^ n| := by
  rw [abs_pow]
  exact h

/-! ### R27. `abs_sub_comm` · `|a - b| = |b - a|` · goal; `abs_sub_comm a b` fixes the direction -/
example (a b : ℝ) (P : ℝ → Prop) (h : P |b - a|) : P |a - b| := by
  rw [abs_sub_comm a b]
  exact h

/-! ### R28. `div_le_iff₀` · `0 < c → (b / c ≤ a ↔ b ≤ a * c)` · goal: the division is multiplied out -/
example (a b c : ℝ) (hc : 0 < c) (h : b ≤ a * c) : b / c ≤ a := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R29. `calc` · goal `a ≤ d` → one goal per step `a ≤ b`, `b = c`, `c ≤ d` -/
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : b = c) (h₃ : c ≤ d) : a ≤ d := by
  calc a ≤ b := by exact h₁
    _ = c := by exact h₂
    _ ≤ d := by exact h₃

/-! ### R30. `gcongr` · goal `f a * c ≤ b * c` → `f a ≤ b`; it proves the side goal `0 ≤ c` itself -/
example (f : ℝ → ℝ) (a b c : ℝ) (hc : 0 ≤ c) (h : ∀ t, f t ≤ b) : f a * c ≤ b * c := by
  gcongr
  exact h a

/-! ## Part 5 · The scaled step -/

/-! ### R31. `positivity` · closes `0 ≤ e` / `0 < e` for `e` built from `+ * / ^ |·|` and the context's sign facts -/
example (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / (2 * b) * |x| ^ 2 := by
  positivity

/-! ## Part 6 · Iterating -/

/-! ### R32. `induction n` · goal list: case `zero` (`n := 0`) and case `succ` (`n := n✝ + 1`, IH `a✝`)
`induction n with | zero => … | succ n ih => …` does the same and names `n✝`, `a✝` as `n`, `ih` (W3). -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : ℕ) : P n := by
  induction n
  case zero => exact h0
  case succ n ih => exact hs n ih

/-! ### R33. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · context gains it -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) (G : Prop) (hG : a * b ≤ a * c → G) : G := by
  have h := mul_le_mul_of_nonneg_left hbc ha
  exact hG h

/-! ### R34. `simpa using e` · closes the goal once `simp` makes it and `e` agree
Here `simp` uses `Function.iterate_zero` (`g^[0] = id`), `id_eq`, `pow_zero`, `pow_one`. -/
example (g : ℝ → ℝ) (a q : ℝ) (e : a ≤ q) : g^[0] a ≤ q ^ 2 ^ 0 := by
  simpa using e

/-! ### R35. `Function.iterate_succ_apply'` · `g^[n + 1] a = g (g^[n] a)` · goal: peel the last step -/
example (g : ℝ → ℝ) (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (g (g^[n] a))) : P (g^[n + 1] a) := by
  rw [Function.iterate_succ_apply']
  exact h

/-! ### R36. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal -/
example (q : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (q ^ (2 ^ n * 2))) : P (q ^ 2 ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R37. `pow_mul` · `a ^ (m * n) = (a ^ m) ^ n` · goal -/
example (q : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P ((q ^ 2 ^ n) ^ 2)) : P (q ^ (2 ^ n * 2)) := by
  rw [pow_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Degree-0 Taylor (the mean value theorem): R4 with `n := 0`, R14, R15, R16 -/
example (g : ℝ → ℝ) (a b : ℝ) (hab : a ≠ b) (hg : ContDiff ℝ 1 g) :
    ∃ ξ, g b = g a + deriv g ξ * (b - a) := by
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 0) hab hg.contDiffOn
  refine ⟨ξ, ?_⟩
  rw [taylor_within_zero_eval] at hξ
  norm_num at hξ
  linear_combination hξ

/-! ### W2. Absolute values of a quotient, then clear the denominator: R24, R26, R23, R28 -/
example (a b c : ℝ) (hc : 0 < |c|) (h : |a| * |b| ^ 3 ≤ 5 * |c|) : |a * b ^ 3 / c| ≤ 5 := by
  rw [abs_div, abs_mul, abs_pow, div_le_iff₀ hc]
  exact h

/-! ### W3. Squaring at each step doubles the exponent: R32, R34, R36, R37, R29, R30 -/
example (e : ℕ → ℝ) (q : ℝ) (hpos : ∀ n, 0 ≤ e n) (h0 : e 0 ≤ q)
    (hstep : ∀ n, e (n + 1) ≤ e n ^ 2) (n : ℕ) : e n ≤ q ^ 2 ^ n := by
  induction n with
    | zero => simpa using h0
    | succ n ih =>
      rw [pow_succ, pow_mul]
      have := hpos n
      calc e (n + 1) ≤ e n ^ 2 := hstep n
        _ ≤ (q ^ 2 ^ n) ^ 2 := by gcongr

end H065Guide

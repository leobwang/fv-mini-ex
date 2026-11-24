/- Guide for H038 (Division with remainder in ℤ[i]).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`ℤ√2`, other bounds).
Assumed: Lean basics (E001–E033). Mathlib names are explained in cheatsheet.md.
-/
import Mathlib

namespace H038Guide

/-! # Part R · Reference entries -/

/-! ## Integer division facts (`/` and `%` on `ℤ`) -/

/-! ### R1. `Int.emod_nonneg a hb.ne'` · context gains `0 ≤ a % b`
`Int.emod_nonneg : b ≠ 0 → 0 ≤ a % b`. From `hb : 0 < b`, `hb.ne'` is `b ≠ 0` (`LT.lt.ne'`). -/
example (a b : ℤ) (hb : 0 < b) (G : Prop) (g : 0 ≤ a % b → G) : G := by
  have h := Int.emod_nonneg a hb.ne'
  exact g h

/-! ### R2. `Int.emod_lt_of_pos a hb` · context gains `a % b < b` -/
example (a b : ℤ) (hb : 0 < b) (G : Prop) (g : a % b < b → G) : G := by
  have h := Int.emod_lt_of_pos a hb
  exact g h

/-! ### R3. `Int.emod_add_mul_ediv a b` · context gains `a % b + b * (a / b) = a` (no hypothesis) -/
example (a b : ℤ) (G : Prop) (g : a % b + b * (a / b) = a → G) : G := by
  have h := Int.emod_add_mul_ediv a b
  exact g h

/-! ## Case split and linear arithmetic -/

/-! ### R4. `by_cases h : p` · goal list: one goal → two, with `h : p` and with `h : ¬p` -/
example (p G : Prop) (g1 : p → G) (g2 : ¬p → G) : G := by
  by_cases h : p
  · exact g1 h
  · exact g2 h

/-! ### R5. `linarith` · closes a linear (in)equality that follows from hypotheses by adding them up
Products of two variables are atoms: `n * (u / n)` is one unknown to `linarith`. -/
example (a b c : ℤ) (h1 : a + b = c) (h2 : 0 ≤ b) : a ≤ c := by
  linarith

/-! ### R6. `rw [show e₁ = e₂ by linarith]` · goal: `e₁` → `e₂`, the equation proved on the spot -/
example (x y z : ℤ) (h : x + y = z) (P : ℤ → Prop) (hp : P y) : P (z - x) := by
  rw [show z - x = y by linarith]
  exact hp

/-! ## Absolute value `|x|` -/

/-! ### R7. `abs_of_nonneg` · `0 ≤ x → |x| = x` · goal: `|x|` → `x` -/
example (x : ℤ) (hx : 0 ≤ x) (P : ℤ → Prop) (h : P x) : P |x| := by
  rw [abs_of_nonneg hx]
  exact h

/-! ### R8. `push Not at h` · context: `h : ¬a ≤ b` → `h : b < a` (pushes `¬` inward) -/
example (a b : ℤ) (h : ¬a ≤ b) (G : Prop) (g : b < a → G) : G := by
  push Not at h
  exact g h

/-! ### R9. `abs_of_neg` · `x < 0 → |x| = -x` · goal: `|x|` → `-x`
In the exercise the hypothesis is proved inline: `abs_of_neg (by linarith)`. -/
example (x : ℤ) (hx : x < 0) (P : ℤ → Prop) (h : P (-x)) : P |x| := by
  rw [abs_of_neg hx]
  exact h

/-! ## The ring `ℤ√d` and its norm (`GaussianInt` is `ℤ√(-1)`) -/

/-! ### R10. `Zsqrtd.norm_eq_mul_conj` · `↑x.norm = x * star x` · goal: the norm cast into `ℤ√d` → a product -/
example {d : ℤ} (x : ℤ√d) (P : ℤ√d → Prop) (h : P (x * star x)) : P (x.norm : ℤ√d) := by
  rw [Zsqrtd.norm_eq_mul_conj]
  exact h

/-! ### R11. `ring` in `ℤ√d` · closes an identity of commutative rings; `star x` is just another unknown -/
example {d : ℤ} (x y z : ℤ√d) : (x - y) * star z = x * star z - y * star z := by
  ring

/-! ### R12. `rw [← Zsqrtd.norm_conj x]` · `(star x).norm = x.norm`, right to left · goal: every `x.norm` → `(star x).norm` -/
example {d : ℤ} (x : ℤ√d) (P : ℤ → Prop) (h : P (star x).norm) : P x.norm := by
  rw [← Zsqrtd.norm_conj x]
  exact h

/-! ### R13. `rw [← Zsqrtd.norm_mul]` · `(x * y).norm = x.norm * y.norm`, right to left · goal: product of norms → norm of a product -/
example {d : ℤ} (x y : ℤ√d) (P : ℤ → Prop) (h : P (x * y).norm) : P (x.norm * y.norm) := by
  rw [← Zsqrtd.norm_mul]
  exact h

/-! ### R14. `Zsqrtd.norm_def` · `x.norm = x.re * x.re - d * x.im * x.im` · goal: the norm → coordinates
For `GaussianInt`, `d = -1` and Lean prints the norm as `Zsqrtd.norm x`. -/
example (x : GaussianInt) (P : ℤ → Prop) (h : P (x.re * x.re - -1 * x.im * x.im)) : P x.norm := by
  rw [Zsqrtd.norm_def]
  exact h

/-! ### R15. `simp` on `.re` / `.im` · goal: coordinates of `+ - *`, `star`, casts `↑n` and `⟨s, t⟩` computed
`simp` uses `Zsqrtd.re_sub`, `Zsqrtd.re_mul`, `Zsqrtd.re_star`, `Zsqrtd.im_star`, `Zsqrtd.smul_val`, … -/
example (x y : GaussianInt) (n s t : ℤ) (P : ℤ → Prop) (h : P (x.re * y.re + x.im * y.im - n * s)) :
    P (x * star y - (n : GaussianInt) * ⟨s, t⟩).re := by
  simp
  exact h

/-! ### R16. `GaussianInt.norm_pos` · `0 < x.norm ↔ x ≠ 0` · `.mpr` turns `x ≠ 0` into `0 < x.norm` -/
example (x : GaussianInt) (hx : x ≠ 0) (G : Prop) (g : 0 < x.norm → G) : G := by
  have h : 0 < x.norm := GaussianInt.norm_pos.mpr hx
  exact g h

/-! ## Using the milestones -/

/-! ### R17. `obtain ⟨s, hs⟩ := e` · context: `e : ∃ s, Q s` → a witness `s` and `hs : Q s` -/
example (Q : ℤ → Prop) (e : ∃ s, Q s) (G : Prop) (g : ∀ s, Q s → G) : G := by
  obtain ⟨s, hs⟩ := e
  exact g s hs

/-! ### R18. `refine ⟨w₁, w₂, by ring, ?_⟩` · goal `∃ q r, A ∧ B` → `B` with the witnesses filled in
`⟨s, t⟩ : GaussianInt` is `s + t·i`; Lean prints it as `{ re := s, im := t }`. -/
example (s t : ℤ) (n : GaussianInt) (P : GaussianInt → GaussianInt → Prop)
    (h : P ⟨s, t⟩ (n - ⟨s, t⟩)) : ∃ q r : GaussianInt, n = q + r ∧ P q r := by
  refine ⟨⟨s, t⟩, n - ⟨s, t⟩, by ring, ?_⟩
  exact h

/-! ## Squares and nonlinear arithmetic -/

/-! ### R19. `sq_abs x` · context gains `|x| ^ 2 = x ^ 2` -/
example (x : ℤ) (G : Prop) (g : |x| ^ 2 = x ^ 2 → G) : G := by
  have h := sq_abs x
  exact g h

/-! ### R20. `abs_nonneg x` · context gains `0 ≤ |x|` -/
example (x : ℤ) (G : Prop) (g : 0 ≤ |x| → G) : G := by
  have h := abs_nonneg x
  exact g h

/-! ### R21. `nlinarith [f₁, f₂]` · closes a polynomial (in)equality; it multiplies hypotheses and the
facts `fᵢ` in pairs, then runs `linarith` -/
example (x y : ℤ) (h1 : 0 ≤ x) (h2 : x ≤ y) : x * x ≤ y * y := by
  nlinarith [h1, h2]

/-! ### R22. `by_contra h` · goal `G` → `False`, context gains `h : ¬G` -/
example (G : Prop) (g : ¬¬G) : G := by
  by_contra h
  exact g h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A bound on `|x|` → a bound on `x ^ 2`: R19, R20, R21 -/
example (x : ℤ) (h : 3 * |x| ≤ 6) : x ^ 2 ≤ 4 := by
  nlinarith [sq_abs x, abs_nonneg x]

/-! ### W2. A norm in `ℤ√2`, by coordinates: R14 then R15 -/
example : (⟨3, 2⟩ : ℤ√2).norm = 1 := by
  rw [Zsqrtd.norm_def]
  simp

/-! ### W3. Norm of a product with a conjugate in `ℤ√2`: R13 and R12, both left to right -/
example (x y : ℤ√2) : (x * star y).norm = x.norm * y.norm := by
  rw [Zsqrtd.norm_mul]
  rw [Zsqrtd.norm_conj]

/-! ### W4. Strict `<` by contradiction: R22, R8, R21 -/
example (x n : ℤ) (hn : 0 < n) (h : x * n < n * n) : x < n := by
  by_contra hx
  push Not at hx
  nlinarith

end H038Guide

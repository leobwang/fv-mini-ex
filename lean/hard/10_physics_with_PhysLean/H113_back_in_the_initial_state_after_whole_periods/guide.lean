/- Guide for H113 (Back in the initial state exactly after whole periods).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact (`real_inner_self_nonneg`, `congrArg …`, `h.ne'`) use `have h := …`, so
the context gains `h` and you can read off exactly what was produced.
Part W: worked combinations on equations that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution

open ClassicalMechanics HarmonicOscillator Time Real InnerProductSpace

namespace H113Guide

/-! # Part R · Reference entries -/

/-! ## Positivity facts: inner products, `ω`, powers -/

/-! ### R1. `real_inner_self_nonneg` · context gains `0 ≤ ⟪x, x⟫_ℝ`
`x` is implicit: Lean finds it from the type you write in `have h : 0 ≤ ⟪x, x⟫_ℝ := …`. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) : 0 ≤ ⟪x, x⟫_ℝ := by
  have h : 0 ≤ ⟪x, x⟫_ℝ := real_inner_self_nonneg
  exact h

/-! ### R2. `HarmonicOscillator.ω_pos` · context gains `0 < S.ω` (write `S.ω_pos`) -/
example (S : HarmonicOscillator) : 0 < S.ω := by
  have h := S.ω_pos
  exact h

/-! ### R3. `pow_pos` · `0 < a → ∀ n, 0 < a ^ n` · context gains `0 < a ^ n` -/
example (a : ℝ) (ha : 0 < a) (n : ℕ) : 0 < a ^ n := by
  have h := pow_pos ha n
  exact h

/-! ### R4. `rcases h with h | h` · goal list: one goal per side of `∨`; context: `h` is that side -/
example (A B G : Prop) (ka : A → G) (kb : B → G) (hab : A ∨ B) : G := by
  rcases hab with h | h
  · exact ka h
  · exact kb h

/-! ### R5. `real_inner_self_pos` · `0 < ⟪x, x⟫_ℝ ↔ x ≠ 0`; `.mpr hx` turns `hx : x ≠ 0` into positivity -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) (hx : x ≠ 0) :
    0 < ⟪x, x⟫_ℝ := by
  have h := real_inner_self_pos.mpr hx
  exact h

/-! ### R6. `nlinarith [p₁, p₂]` · closes a polynomial (in)equality from hypotheses and the extra
facts `pᵢ`; it also multiplies pairs of them, which `linarith` (R20) never does. -/
example (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) : 0 < a + b * c := by
  nlinarith [mul_pos hb hc]

/-! ## The oscillator's formulas -/

/-! ### R7. `rw [InitialConditions.trajectory_eq] at hx` · context: `hx` mentions the formula
`IC.trajectory S = fun t => cos (S.ω * t.val) • IC.x₀ + (sin (S.ω * t.val) / S.ω) • IC.v₀`. -/
example (IC : InitialConditions) (S : HarmonicOscillator) (t : Time) (y : EuclideanSpace ℝ (Fin 1))
    (hx : IC.trajectory S t = y) :
    cos (S.ω * t.val) • IC.x₀ + (sin (S.ω * t.val) / S.ω) • IC.v₀ = y := by
  rw [InitialConditions.trajectory_eq] at hx
  exact hx

/-! ### R8. `rw [InitialConditions.trajectory_velocity] at hv` · context: `hv` mentions the velocity
`∂ₜ (IC.trajectory S) = fun t => -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀`. -/
example (IC : InitialConditions) (S : HarmonicOscillator) (t : Time) (y : EuclideanSpace ℝ (Fin 1))
    (hv : ∂ₜ (IC.trajectory S) t = y) :
    -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀ = y := by
  rw [InitialConditions.trajectory_velocity] at hv
  exact hv

/-! ## From a vector equation to scalar equations -/

/-! ### R9. `congrArg (fun w => ⟪a, w⟫_ℝ) h` · context gains `⟪a, u⟫_ℝ = ⟪a, v⟫_ℝ` from `h : u = v`
"Apply the same function to both sides". It turns an equation of vectors into one of reals. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a u v : E) (h : u = v) :
    ⟪a, u⟫_ℝ = ⟪a, v⟫_ℝ := by
  have h' := congrArg (fun w => ⟪a, w⟫_ℝ) h
  exact h'

/-! ### R10. `simp only at h` · context: β-reduces `(fun x => body) a` to `body` with `a` put in
`simp only [R11, R12] at h` does this on its own; `rw` does not, so it cannot see inside first. -/
example {E : Type} (f : ℝ → E) (s : ℝ) (P : E → Prop) (h : P ((fun r => f r) s)) : P (f s) := by
  simp only at h
  exact h

/-! ### R11. `inner_add_right` · `⟪x, y + z⟫_ℝ = ⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ` · goal (or `at h`) -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y z : E) (P : ℝ → Prop)
    (h : P (⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ)) : P ⟪x, y + z⟫_ℝ := by
  rw [inner_add_right]
  exact h

/-! ### R12. `real_inner_smul_right` · `⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ` · goal (or `at h`) -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) (r : ℝ)
    (P : ℝ → Prop) (h : P (r * ⟪x, y⟫_ℝ)) : P ⟪x, r • y⟫_ℝ := by
  rw [real_inner_smul_right]
  exact h

/-! ### R13. `real_inner_comm x y` · `⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ` · goal: swaps the two arguments
Its explicit arguments are in the order of the RIGHT side: `real_inner_comm x y` turns `⟪y, x⟫` into `⟪x, y⟫`. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) (P : ℝ → Prop)
    (h : P ⟪x, y⟫_ℝ) : P ⟪y, x⟫_ℝ := by
  rw [real_inner_comm x y]
  exact h

/-! ## Algebra with a nonzero denominator -/

/-! ### R14. `HarmonicOscillator.ω_ne_zero` · context gains `S.ω ≠ 0` (write `S.ω_ne_zero`) -/
example (S : HarmonicOscillator) : S.ω ≠ 0 := by
  have h := S.ω_ne_zero
  exact h

/-! ### R15. `field_simp at h` · context: `h` with every `/ c` cleared, using `hc : c ≠ 0` from the
context. It multiplies both sides through; the result is put in its own normal form (read it off). -/
example (a b c x y : ℝ) (hc : c ≠ 0) (h : a * x + b / c * y = x) : a * x * c + b * y = x * c := by
  field_simp at h
  exact h

/-! ### R16. `linear_combination e₁ * h₁ + h₂` · closes `L = R` when `L - R` equals
`e₁ * (lhs₁ - rhs₁) + (lhs₂ - rhs₂)` as polynomials (checked by `ring`). `eᵢ` are any terms. -/
example (a b x : ℝ) (h₁ : a * x = b) (h₂ : x = 1) : a = b := by
  linear_combination h₁ - a * h₂

/-! ## Using a product that is zero -/

/-! ### R17. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp hab` gives the `∨` (split it with R4) -/
example (a b : ℝ) (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  have h := mul_eq_zero.mp hab
  exact h

/-! ### R18. `h.ne'` (lemma `LT.lt.ne'`) · context gains `a ≠ 0` from `h : 0 < a` -/
example (a : ℝ) (ha : 0 < a) : a ≠ 0 := by
  have h := ha.ne'
  exact h

/-! ### R19. `absurd h hne` · closes ANY goal from `h : A` and `hne : ¬A` (`a ≠ 0` is `¬(a = 0)`) -/
example (a : ℝ) (G : Prop) (h : a = 0) (hne : a ≠ 0) : G := by
  exact absurd h hne

/-! ### R20. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (c : ℝ) (h : c - 1 = 0) : c = 1 := by
  linarith

/-! ## Casts, `cos`, `sin` at multiples of `π` -/

/-! ### R21. `push_cast` · goal: casts `↑(…)` of `ℤ` into `ℝ` pushed down to the variables -/
example (n m : ℤ) (P : ℝ → Prop) (h : P (3 * ↑n + ↑m)) : P ↑(3 * n + m) := by
  push_cast
  exact h

/-! ### R22. `field_simp` · goal: every `/ c` cleared, using `hc : c ≠ 0` (in context, or passed
as `field_simp [hc]`); it closes the goal if what is left is trivial. -/
example (a b c : ℝ) (hc : c ≠ 0) (h : a * b = b * c) : a * (b / c) = b := by
  field_simp
  exact h

/-! ### R23. `Real.cos_eq_one_iff` · `cos x = 1 ↔ ∃ n : ℤ, ↑n * (2 * π) = x` · goal
`(Real.cos_eq_one_iff x).mp h` goes the other way: from `h : cos x = 1` to the `∃`. -/
example (x : ℝ) (k : ℤ) (hk : ↑k * (2 * π) = x) : cos x = 1 := by
  rw [Real.cos_eq_one_iff]
  exact ⟨k, hk⟩

/-! ### R24. `Real.sin_int_mul_pi` · `sin (↑n * π) = 0` for `n : ℤ` · goal -/
example (n : ℤ) (P : ℝ → Prop) (h : P 0) : P (sin (↑n * π)) := by
  rw [Real.sin_int_mul_pi]
  exact h

/-! ## Collapsing the formulas when `cos = 1`, `sin = 0` -/

/-! ### R25. `simp only [hc, hs]` · goal: `cos θ` → `1` and `sin θ` → `0` (hypotheses as rewrite rules)
It also β-reduces, like R10. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (θ w : ℝ) (x v : E)
    (hc : cos θ = 1) (hs : sin θ = 0) (P : E → Prop) (h : P ((0 / w) • x + (1 : ℝ) • v)) :
    P ((sin θ / w) • x + cos θ • v) := by
  simp only [hc, hs]
  exact h

/-! ### R26. `simp` · closes what is left: `zero_div`, `zero_smul`, `one_smul`, `zero_add`, `smul_zero`
`simp [hc, hs]` does R25 and R26 in one call. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : ℝ) (x v : E) :
    (0 / w) • x + (1 : ℝ) • v = v := by
  simp

/-! ## The `↔` and its two directions -/

/-! ### R27. `constructor` on `A ↔ B` · goal list: `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  constructor
  · exact f
  · exact g

/-! ### R28. `rintro ⟨ha, hb⟩` · goal `A ∧ B → C` → `C`; context gains `ha : A`, `hb : B`
The same pattern takes apart `∃`: `rintro ⟨n, hn⟩` on `(∃ n, Q n) → C`. -/
example (A B C : Prop) (k : A → B → C) : A ∧ B → C := by
  rintro ⟨ha, hb⟩
  exact k ha hb

/-! ### R29. `obtain ⟨n, hn⟩ := h` · context: `h : ∃ n, Q n` → `n` and `hn : Q n` -/
example (Q : ℤ → Prop) (G : Prop) (h : ∃ n, Q n) (k : ∀ n, Q n → G) : G := by
  obtain ⟨n, hn⟩ := h
  exact k n hn

/-! # Part W · Worked combinations (not the exercise's equations) -/

/-! ### W1. Pair a vector equation with a vector: R9, then R11, R12 in one `simp only` (R10 built in) -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : ℝ) (x y : E)
    (h : a • x + b • y = y) : a * ⟪y, x⟫_ℝ + b * ⟪y, y⟫_ℝ = ⟪y, y⟫_ℝ := by
  have h' := congrArg (fun w => ⟪y, w⟫_ℝ) h
  simp only [inner_add_right, real_inner_smul_right] at h'
  exact h'

/-! ### W2. Eliminate a cross term, factor, and cancel a positive factor: R16, R17, R4, R19, R20 -/
example (p q r c : ℝ) (hp : 0 < p) (h₁ : c * p + r = p) (h₂ : c * q - r = q) (hq : 0 ≤ q) :
    c = 1 := by
  have key : (p + q) * (c - 1) = 0 := by linear_combination h₁ + h₂
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (add_pos_of_pos_of_nonneg hp hq).ne'
  · linarith

/-! ### W3. `cos = 1` at a multiple of `4π`: R23, then the witness with R21 and `ring` -/
example (k : ℤ) : cos (↑k * (4 * π)) = 1 := by
  rw [Real.cos_eq_one_iff]
  exact ⟨2 * k, by push_cast; ring⟩

/-! ### W4. Clear a denominator in a goal, then use an equation: R22, R16 -/
example (a b c : ℝ) (hc : c ≠ 0) (h : a * 3 = c * b) : a * (3 / c) = b := by
  field_simp
  linear_combination h

end H113Guide

/- Guide for H072 (Global error of Euler's method).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G` is
any goal; a hypothesis `hG` or `h` in an entry is only there to finish the example and shows what the
goal or context became.
Part W: worked combinations on objects that are NOT the exercise's (a derivative bound instead of a
Lipschitz derivative, a perturbed iteration instead of Euler's method, `x ^ n` instead of `(1 + a) ^ n`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H072Guide

/-! # Part R · Reference entries -/

/-! ## Derivatives, continuity and the mean value theorem -/

/-! ### R1. `continuous_iff_continuousAt` · goal: `Continuous f` → `∀ x, ContinuousAt f x` -/
example (f : ℝ → ℝ) (h : ∀ x, ContinuousAt f x) : Continuous f := by
  rw [continuous_iff_continuousAt]
  exact h

/-! ### R2. `HasDerivAt.continuousAt` · closes `ContinuousAt f x` from `hf : HasDerivAt f f' x`
Term form: `hf.continuousAt`. Combined with R1: `continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt`. -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) : ContinuousAt f x := by
  exact hf.continuousAt

/-! ### R3. `Continuous.continuousOn` · closes `ContinuousOn f s` from `hf : Continuous f` -/
example (f : ℝ → ℝ) (s : Set ℝ) (hf : Continuous f) : ContinuousOn f s := by
  exact hf.continuousOn

/-! ### R4. `linarith` · closes a linear (in)equality that follows from the hypotheses
`linarith [t₁, t₂]` also uses the extra facts `tᵢ`. Inline: `(show a < a + s by linarith)`. -/
example (a s : ℝ) (hs : 0 < s) : a < a + s := by
  linarith

/-! ### R5. `∀ x ∈ S, Q x` from `h : ∀ x, Q x` · term `fun x _ => h x` (the `_` ignores `x ∈ S`) -/
example (S : Set ℝ) (Q : ℝ → Prop) (h : ∀ x, Q x) : ∀ x ∈ S, Q x := by
  intro x _
  exact h x

/-! ### R6. `exists_hasDerivAt_eq_slope` (mean value theorem) + `obtain` · context gains `c hc hslope` -/
example (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (G : Prop)
    (hG : ∀ c, c ∈ Set.Ioo a b → f' c = (f b - f a) / (b - a) → G) : G := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hab hfc hff'
  exact hG c hc hslope

/-! ## Algebra on the slope -/

/-! ### R7. `rw [show u = v by ring]` · goal: rewrite with a fact proved on the spot -/
example (a s : ℝ) (P : ℝ → Prop) (h : P s) : P (a + s - a) := by
  rw [show a + s - a = s by ring]
  exact h

/-! ### R8. `mul_sub` · `a * (b - c) = a * b - a * c` -/
example {α : Type} [CommRing α] (a b c : α) (P : α → Prop) (h : P (a * b - a * c)) :
    P (a * (b - c)) := by
  rw [mul_sub]
  exact h

/-! ### R9. `LT.lt.ne'` · `hab : a < b` gives `hab.ne' : b ≠ a`; so `hs : 0 < s` gives `hs.ne' : s ≠ 0` -/
example {α : Type} [Preorder α] (a b : α) (hab : a < b) (G : Prop) (hG : b ≠ a → G) : G := by
  have hne : b ≠ a := hab.ne'
  exact hG hne

/-! ### R10. `mul_div_cancel₀` · `b ≠ 0 → b * (a / b) = a` -/
example {α : Type} [Field α] (a b : α) (hb : b ≠ 0) (P : α → Prop) (h : P a) :
    P (b * (a / b)) := by
  rw [mul_div_cancel₀ _ hb]
  exact h

/-! ## Absolute values and inequalities -/

/-! ### R11. `abs_nonneg` + `.trans` · `(abs_nonneg x).trans h : 0 ≤ c` from `h : |x| ≤ c` -/
example (x c : ℝ) (h : |x| ≤ c) (G : Prop) (hG : 0 ≤ c → G) : G := by
  have hc : 0 ≤ c := (abs_nonneg x).trans h
  exact hG hc

/-! ### R12. `simp at h` / `simpa using h` · context: `h` simplified (`x + 1 - x` → `1`, `K * 1` → `K`)
`simpa using h` simplifies both `h` and the goal, then closes the goal with `h`. `simp` also knows `|1| = 1`. -/
example (K x : ℝ) (h : 0 < K * (x + 1 - x)) : 0 < K := by
  simp at h
  exact h

/-! ### R13. `hc.1`, `hc.2` · `hc : c ∈ Set.Ioo a b` unfolds to `a < c ∧ c < b` (`Set.mem_Ioo`) -/
example (a b c : ℝ) (hc : c ∈ Set.Ioo a b) (G : Prop) (hG : a < c → c < b → G) : G := by
  have h1 : a < c := hc.1
  have h2 : c < b := hc.2
  exact hG h1 h2

/-! ### R14. `abs_of_pos` · `0 < a → |a| = a` -/
example (a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ### R15. `abs_mul` · `|a * b| = |a| * |b|` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R16. `calc` · goal `a ≤ d` proved as a chain `a ≤ b`, `b ≤ c`, `c = d` -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c = d) : a ≤ d := by
  calc a ≤ b := h1
    _ ≤ c := h2
    _ = d := h3

/-! ### R17. `gcongr` · goal `c * x ≤ c * y` → `x ≤ y`; the side goal `0 ≤ c` is closed from `hc` -/
example (c y z : ℝ) (f : ℝ → ℝ) (hc : 0 ≤ c) (hf : ∀ w, f w ≤ y) : c * f z ≤ c * y := by
  gcongr
  exact hf z

/-! ## One step of a recursive sequence -/

/-- A perturbed iteration `u₀ = a`, `uₙ₊₁ = g uₙ + d` (not the exercise's sequence). -/
def walk (a d : ℝ) (g : ℝ → ℝ) : ℕ → ℝ
  | 0 => a
  | n + 1 => g (walk a d g n) + d

/-! ### R18. `simp only [walk]` · goal: `walk a d g (k + 1)` → its defining equation (one step) -/
example (a d : ℝ) (g : ℝ → ℝ) (k : ℕ) (P : ℝ → Prop) (h : P (g (walk a d g k) + d)) :
    P (walk a d g (k + 1)) := by
  simp only [walk]
  exact h

/-! ### R19. `set u := e` · context gains `u : ℝ := e`; every `e` in the goal becomes `u` -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : ∀ v, P v v) : P (a * b + 1) (a * b + 1) := by
  set u := a * b + 1
  exact h u

/-! ### R20. `push_cast` · goal: `↑(k + 1)` (cast of a natural-number sum) → `↑k + 1` -/
example (k : ℕ) (P : ℝ → Prop) (h : P (↑k + 1)) : P ((k + 1 : ℕ) : ℝ) := by
  push_cast
  exact h

/-! ### R21. `abs_add_le` · `|a + b| ≤ |a| + |b|` (triangle inequality) -/
example (a b : ℝ) (G : Prop) (hG : |a + b| ≤ |a| + |b| → G) : G := by
  have h := abs_add_le a b
  exact hG h

/-! ### R22. `gcongr` on a sum · goal `p + q ≤ p' + q'` → goals `p ≤ p'` and `q ≤ q'`
A summand that is the same on both sides produces no goal. -/
example (f g : ℝ → ℝ) (x c d : ℝ) (hf : ∀ w, f w ≤ c) (hg : ∀ w, g w ≤ d) :
    f x + g x ≤ c + d := by
  gcongr
  · exact hf x
  · exact hg x

/-! ## Powers and the exponential -/

/-! ### R23. `one_le_pow₀` · `1 ≤ a → 1 ≤ a ^ n` -/
example (a : ℝ) (ha : 1 ≤ a) (n : ℕ) (G : Prop) (hG : 1 ≤ a ^ n → G) : G := by
  have h1 : 1 ≤ a ^ n := one_le_pow₀ ha
  exact hG h1

/-! ### R24. `pow_succ` · `a ^ (n + 1) = a ^ n * a` -/
example {α : Type} [Monoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R25. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` (a term for `nlinarith`) -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) (G : Prop) (hG : a * b ≤ a * c → G) : G := by
  have h := mul_le_mul_of_nonneg_left hbc ha
  exact hG h

/-! ### R26. `nlinarith [t₁, …]` · closes a goal that needs products of hypotheses
It multiplies pairs of hypotheses (and the extra facts `tᵢ`) and then runs `linarith`. -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) : x ≤ x * y := by
  nlinarith

/-! ### R27. `gcongr` · goal `x * c ≤ y * c` → `x ≤ y`; the side goal `0 ≤ c` is closed from `hc` -/
example (c y z : ℝ) (f : ℝ → ℝ) (hc : 0 ≤ c) (hf : ∀ w, f w ≤ y) : f z * c ≤ y * c := by
  gcongr
  exact hf z

/-! ### R28. `Real.add_one_le_exp` · `x + 1 ≤ Real.exp x` for every real `x` -/
example (x : ℝ) (G : Prop) (hG : x + 1 ≤ Real.exp x → G) : G := by
  have h := Real.add_one_le_exp x
  exact hG h

/-! ### R29. `gcongr` on powers · goal `x ^ n ≤ y ^ n` → `x ≤ y`; the side goal `0 ≤ x` is closed from `hx` -/
example (y z : ℝ) (n : ℕ) (f : ℝ → ℝ) (hx : 0 ≤ f z) (hf : ∀ w, f w ≤ y) : f z ^ n ≤ y ^ n := by
  gcongr
  exact hf z

/-! ### R30. `Real.exp_nat_mul` · `Real.exp (↑n * x) = Real.exp x ^ n`; right to left: `rw [← Real.exp_nat_mul]` -/
example (x : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (Real.exp (↑n * x))) : P (Real.exp x ^ n) := by
  rw [← Real.exp_nat_mul]
  exact h

/-! ## Using a general lemma at a specific sequence -/

/-! ### R31. `have := lem (fun k => …) …` · context gains `this`, with the function's body substituted -/
example (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (lem : ∀ e : ℕ → ℝ, (∀ n, 0 ≤ e n) → e 3 ≤ e 3 + e 0) (G : Prop)
    (hG : f 3 + f 3 ≤ f 3 + f 3 + (f 0 + f 0) → G) : G := by
  have := lem (fun k => f k + f k) (fun n => add_nonneg (hf n) (hf n))
  exact hG this

/-! ### R32. `positivity` · closes `0 ≤ e` or `0 < e` for `e` built from `+ * ^ |·|`, numerals and atoms
with a hypothesis `0 ≤ x` / `0 < x` in the context -/
example (s L K : ℝ) (hs : 0 < s) (hL : 0 ≤ L) (hK : 0 ≤ K) : 0 ≤ s * L + K * s ^ 2 := by
  positivity

/-! ### R33. `simpa [walk] using this` · `this` cleaned up: `↑0 * s` → `0`, `walk … 0` → its start value,
`v - v` → `0`, `0 + x` → `x` (and `|0|` → `0`); then it closes the (also simplified) goal -/
example (g : ℝ → ℝ) (a s c : ℝ)
    (this : g a ≤ c * ((g (a + ((0 : ℕ) : ℝ) * s) - walk (g a) 0 g 0) + s)) : g a ≤ c * s := by
  simpa [walk] using this

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. One mean-value-theorem step with a bounded derivative: R1–R7, R9, R10, R14–R17 -/
example (f f' : ℝ → ℝ) (K a s : ℝ) (hs : 0 < s) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hK : ∀ x, |f' x| ≤ K) : |f (a + s) - f a| ≤ K * s := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope f f' (show a < a + s by linarith)
    hcont.continuousOn (fun x _ => hf x)
  have e : f (a + s) - f a = s * f' c := by
    rw [hslope, show a + s - a = s by ring, mul_div_cancel₀ _ hs.ne']
  rw [e, abs_mul, abs_of_pos hs]
  calc s * |f' c| ≤ s * K := by gcongr; exact hK c
    _ = K * s := by ring

/-! ### W2. One step of an error recursion: R18, R19, R21, R22 -/
example (g : ℝ → ℝ) (L a b d : ℝ) (hg : ∀ u v, |g u - g v| ≤ L * |u - v|) (k : ℕ) :
    |walk a d g (k + 1) - walk b 0 g (k + 1)| ≤ L * |walk a d g k - walk b 0 g k| + |d| := by
  simp only [walk]
  set u := walk a d g k
  set w := walk b 0 g k
  have key : g u + d - (g w + 0) = (g u - g w) + d := by ring
  rw [key]
  calc _ ≤ |g u - g w| + |d| := abs_add_le _ _
    _ ≤ L * |u - w| + |d| := by gcongr; exact hg u w

/-! ### W3. A power below an exponential: R28, R29, R30 -/
example (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : x ^ n ≤ Real.exp (n * (x - 1)) := by
  calc x ^ n ≤ Real.exp (x - 1) ^ n := by gcongr; linarith [Real.add_one_le_exp (x - 1)]
    _ = Real.exp (n * (x - 1)) := by rw [← Real.exp_nat_mul]

end H072Guide

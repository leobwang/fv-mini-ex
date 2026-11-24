/- Guide for H090 (Gibbs variational principle).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact from a lemma (`div_pos ha hb`, `hz.ne'`, …) use `have h := …`, so the
context gains `h` and you can read off exactly what the lemma produced.
Part W: worked combinations on sums and inequalities that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open CanonicalEnsemble Real

namespace H090Guide

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]

/-! # Part R · Reference entries -/

/-! ## The Boltzmann weights: `∑ p = 1` and `log p` -/

/-! ### R1. `simp only [probabilityBetaReal]` · goal: `p t i` → `rexp (-t * E i) / Z t`
`rw [probabilityBetaReal]` does the same when the term is not under a `∑ i, …` binder. -/
example (𝓒 : CanonicalEnsemble ι) (t : ℝ) (i : ι) (P : ℝ → Prop)
    (h : P (rexp (-t * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal t)) :
    P (𝓒.probabilityBetaReal t i) := by
  simp only [probabilityBetaReal]
  exact h

/-! ### R2. `Finset.sum_div` · `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; `← …` pulls `/ a` out -/
example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) / a)) : P (∑ i, f i / a) := by
  rw [← Finset.sum_div]
  exact h

/-! ### R3. `mathematicalPartitionFunctionBetaReal_pos` · context gains `0 < Z t` (needs `[Nonempty ι]`) -/
example [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)
    (g : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t → G) : G := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos t
  exact g hZ

/-! ### R4. `LT.lt.ne'` · `hz.ne'` turns `hz : 0 < z` into `z ≠ 0` -/
example (z : ℝ) (hz : 0 < z) : z ≠ 0 := by
  have h := hz.ne'
  exact h

/-! ### R5. `div_self` · `a ≠ 0 → a / a = 1` · context gains the equation -/
example (a : ℝ) (ha : a ≠ 0) : a / a = 1 := by
  have h := div_self ha
  exact h

/-! ### R6. `Real.log_div` · `x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y` · goal -/
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (P : ℝ → Prop) (h : P (Real.log x - Real.log y)) :
    P (Real.log (x / y)) := by
  rw [Real.log_div hx hy]
  exact h

/-! ### R7. `Real.exp_pos` · context gains `0 < rexp x` -/
example (x : ℝ) : 0 < rexp x := by
  have h := Real.exp_pos x
  exact h

/-! ### R8. `Real.log_exp` · `log (rexp x) = x` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) : P (Real.log (rexp x)) := by
  rw [Real.log_exp]
  exact h

/-! ## The termwise bound `x (log y - log x) ≤ y - x` -/

/-! ### R9. `rcases hx.eq_or_lt with rfl | hx'` · goal list: `0 ≤ x` → case `x = 0` (substituted), case `0 < x`
`hx.eq_or_lt : 0 = x ∨ 0 < x` (`LE.le.eq_or_lt`); the pattern `rfl` replaces `x` by `0` everywhere. -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h0 : P 0) (hpos : 0 < x → P x) : P x := by
  rcases hx.eq_or_lt with rfl | hx'
  · exact h0
  · exact hpos hx'

/-! ### R10. `simp` on a `0 * …` goal · goal: `0 * c ≤ y - 0` → `0 ≤ y` (`zero_mul`, `sub_zero`) -/
example (c y : ℝ) (hy : 0 ≤ y) : 0 * c ≤ y - 0 := by
  simp
  exact hy

/-! ### R11. `linarith` · closes a linear (in)equality that follows from hypotheses by adding them up
Products such as `x * log y` count as single unknowns. -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b + c ≤ 1) (h3 : 0 ≤ c) : a ≤ 1 := by
  linarith

/-! ### R12. `Real.log_le_sub_one_of_pos` · `0 < x → log x ≤ x - 1` · context gains the bound -/
example (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by
  have h := Real.log_le_sub_one_of_pos hx
  exact h

/-! ### R13. `div_pos` · `0 < a → 0 < b → 0 < a / b` · context gains `0 < a / b` -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  have h := div_pos ha hb
  exact h

/-! ### R14. `rw [Real.log_div hx hy] at h` · context: rewrites inside hypothesis `h`, goal unchanged -/
example (x y c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (h : Real.log (x / y) ≤ c) (G : Prop)
    (g : Real.log x - Real.log y ≤ c → G) : G := by
  rw [Real.log_div hx hy] at h
  exact g h

/-! ### R15. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · context gains it -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c := by
  have h := mul_le_mul_of_nonneg_left hbc ha
  exact h

/-! ### R16. `LT.lt.le` · `h.le` turns `h : a < b` into `a ≤ b` -/
example (a b : ℝ) (hab : a < b) : a ≤ b := by
  have h := hab.le
  exact h

/-! ### R17. `field_simp` · goal: multiplies out denominators it can prove nonzero (from `hz : 0 < z`)
It may close the goal; otherwise finish with `ring`. -/
example (a b z : ℝ) (hz : 0 < z) : a / z + b = (a + b * z) / z := by
  field_simp

example (a b z : ℝ) (hz : 0 < z) (h : a = z * b) : a / z = b := by
  field_simp
  exact h

/-! ## Summing the bound -/

/-! ### R18. `calc` · goal `a ≤ c` → one goal per step `a ≤ b`, `b = c`; `_` is the previous right side -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b = c) : a ≤ c := by
  calc _ ≤ b := ?_
    _ = c := ?_
  exact h1
  exact h2

/-! ### R19. `Finset.sum_le_sum` · goal: `∑ f ≤ ∑ g` → `∀ i ∈ Finset.univ, f i ≤ g i` -/
example (f g : ι → ℝ) (h : ∀ i ∈ Finset.univ, f i ≤ g i) : ∑ i, f i ≤ ∑ i, g i := by
  apply Finset.sum_le_sum
  exact h

/-! ### R20. `Finset.sum_sub_distrib` · `∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i` -/
example (f g : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, f i - ∑ i, g i)) : P (∑ i, (f i - g i)) := by
  rw [Finset.sum_sub_distrib]
  exact h

/-! ### R21. `sub_self` · `a - a = 0` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P 0) : P (a - a) := by
  rw [sub_self]
  exact h

/-! ## Expanding the sums and dividing by `b` -/

/-! ### R22. `simp only [e] at h` with `e : ∀ …, l = r` · context: rewrites `l` inside `∑ i, …` in `h`
`rw` cannot rewrite under the binder `∑ i` when `l` mentions `i`; `simp only` can. -/
example (f g : ι → ℝ) (e : ∀ i, f i = g i) (h : ∑ i, f i ≤ 0) (G : Prop)
    (k : ∑ i, g i ≤ 0 → G) : G := by
  simp only [e] at h
  exact k h

/-! ### R23. `set L := e` · context gains `L : ℝ := e`; every `e` in goal and context → `L` -/
example (x : ℝ) (P : ℝ → Prop) (h : ∀ L, P L) : P (Real.log x) := by
  set L := Real.log x
  exact h L

/-! ### R24. `Finset.sum_congr rfl` · goal: `∑ f = ∑ g` → `∀ x ∈ Finset.univ, f x = g x`
In term mode: `Finset.sum_congr rfl fun i _ => by ring`. -/
example (f g : ι → ℝ) (h : ∀ x ∈ Finset.univ, f x = g x) : ∑ i, f i = ∑ i, g i := by
  apply Finset.sum_congr rfl
  exact h

/-! ### R25. `simp only [Real.negMulLog]` · goal: `negMulLog x` → `-x * log x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (-x * Real.log x)) : P (Real.negMulLog x) := by
  simp only [Real.negMulLog]
  exact h

/-! ### R26. `Finset.sum_add_distrib` · `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i` -/
example (f g : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, f i + ∑ i, g i)) : P (∑ i, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R27. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `← …` pulls `a` out -/
example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (a * ∑ i, f i)) : P (∑ i, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (∑ i, a * f i)) : P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R28. `mul_one` · `a * 1 = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R29. `rw [show A = B by tac]` · goal: `A` → `B`, with `A = B` proved on the spot by `tac` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (b + a)) : P (a + b) := by
  rw [show a + b = b + a by ring]
  exact h

/-! ### R30. `div_le_div_of_nonneg_right` · goal list: `a / c ≤ b / c` → `a ≤ b`, `0 ≤ c` -/
example (a b c : ℝ) (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  apply div_le_div_of_nonneg_right
  exact hab
  exact hc

/-! # Part W · Worked combinations (not the exercise's sums) -/

/-! ### W1. Termwise log bound, summed: R12, R15, R11 inside R19, then R18 → R20 -/
example (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 < a i) (hsum : ∑ i, w i = 1) :
    ∑ i, w i * Real.log (a i) ≤ ∑ i, w i * a i - 1 := by
  calc _ ≤ ∑ i, (w i * a i - w i) :=
        Finset.sum_le_sum fun i _ => by
          have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (ha i)) (hw i)
          linarith
    _ = ∑ i, w i * a i - 1 := by rw [Finset.sum_sub_distrib, hsum]

/-! ### W2. Expand `∑ w (c a + d)` using `∑ w = 1`: R24 + `ring`, then R26, R27 ←, `hsum`, R28 -/
example (w a : ι → ℝ) (c d : ℝ) (hsum : ∑ i, w i = 1) :
    ∑ i, w i * (c * a i + d) = c * ∑ i, w i * a i + d := by
  have h1 : ∑ i, w i * (c * a i + d) = ∑ i, (c * (w i * a i) + d * w i) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one]

/-! ### W3. Divide an inequality by `c > 0`: R29 (with R17), then R30 with R16 -/
example (u a s c : ℝ) (hc : 0 < c) (h : u ≤ c * a - s) : u / c ≤ a - s / c := by
  rw [show a - s / c = (c * a - s) / c by field_simp]
  exact div_le_div_of_nonneg_right h hc.le

end H090Guide

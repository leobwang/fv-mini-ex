/- Guide for E123 (Angular frequency of the oscillator).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `g` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

open ClassicalMechanics

namespace E123Guide

/-! # Part R · Reference entries -/

/-! ## From `ω ^ 2` to the data `k` and `m` -/

/-! ### R1. `HarmonicOscillator.ω_sq` · `S.ω ^ 2 = S.k / S.m` · goal
`S.ω` is defined as `√(S.k / S.m)`; this lemma squares the root away for you. -/
example (S : HarmonicOscillator) (P : ℝ → Prop) (h : P (S.k / S.m)) : P (S.ω ^ 2) := by
  rw [HarmonicOscillator.ω_sq]
  exact h

/-! ### R2. `HarmonicOscillator.m_ne_zero` · `S.m ≠ 0` · context gains `hm : S.m ≠ 0`
Derived from the structure field `S.m_pos : 0 < S.m`. It is a `@[simp]` lemma. -/
example (S : HarmonicOscillator) (G : Prop) (g : S.m ≠ 0 → G) : G := by
  have hm := S.m_ne_zero
  exact g hm

/-! ## Cancelling the mass -/

/-! ### R3. `field_simp [hb]` · clears the denominators it can prove nonzero; here it closes the goal
It proves `b ≠ 0` from the facts in brackets, from hypotheses in context, and from `@[simp]` lemmas. -/
example {K : Type} [Field K] (a b : K) (hb : b ≠ 0) : b * (a / b) = a := by
  field_simp [hb]

/-! ### R4. `mul_div_cancel₀` · `b ≠ 0 → b * (a / b) = a` · closes the goal as a term -/
example {G₀ : Type} [CommGroupWithZero G₀] (a b : G₀) (hb : b ≠ 0) : b * (a / b) = a := by
  exact mul_div_cancel₀ a hb

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Unfolding `ω` instead of using R1 leaves a square root
`unfold HarmonicOscillator.ω` exposes the definition `√(S.k / S.m)`. Squaring it by hand needs
`Real.sq_sqrt` and a proof of `0 ≤ S.k / S.m`; R1 has done exactly that already. -/
example (S : HarmonicOscillator) (P : ℝ → Prop) (h : P √(S.k / S.m)) : P S.ω := by
  unfold HarmonicOscillator.ω
  exact h

/-! ### W2. Another oscillator, an LC circuit: rewrite the squared frequency, then R3 with two facts
Inductance `L`, capacitance `C`, angular frequency `w` with `w ^ 2 = 1 / (L * C)`. The rewrite plays
the role of R1; `field_simp` needs `L ≠ 0` and `C ≠ 0` to clear the denominator `L * C`. -/
example (L C w : ℝ) (hL : L ≠ 0) (hC : C ≠ 0) (hw : w ^ 2 = 1 / (L * C)) : L * C * w ^ 2 = 1 := by
  rw [hw]
  field_simp [hL, hC]

end E123Guide

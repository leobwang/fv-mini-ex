/- Guide for H092 (Third law: a unique ground state).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact from a lemma (`div_pos ha hb`, `hf.sub hg`, …) use `have h := …`, so the
context gains `h` and you can read off exactly what the lemma produced.
`l : Filter β` is "the way the variable moves" (in the exercise `atTop`: `b → ∞`); `𝓝 a` is "close to `a`".
Part W: worked combinations on limits that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open CanonicalEnsemble Real Filter Topology

namespace H092Guide

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]

/-! # Part R · Reference entries -/

/-! ## One Boltzmann weight is at most `exp (-t (E j - E i))` -/

/-! ### R1. `haveI : Nonempty ι := ⟨i⟩` · context gains the instance `Nonempty ι`
Lemmas with a `[Nonempty ι]` argument (R2) find it from then on. -/
example (i : ι) (G : Prop) (g : Nonempty ι → G) : G := by
  haveI : Nonempty ι := ⟨i⟩
  exact g this

/-! ### R2. `mathematicalPartitionFunctionBetaReal_pos` · context gains `0 < Z t` (needs `[Nonempty ι]`) -/
example [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)
    (g : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t → G) : G := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos t
  exact g hZ

/-! ### R3. `Real.exp_pos` · context gains `0 < rexp x` -/
example (x : ℝ) : 0 < rexp x := by
  have h := Real.exp_pos x
  exact h

/-! ### R4. `LT.lt.le` · `h.le` turns `h : a < b` into `a ≤ b` -/
example (a b : ℝ) (hab : a < b) : a ≤ b := by
  have h := hab.le
  exact h

/-! ### R5. `Finset.mem_univ` · context gains `i ∈ Finset.univ` (every element is in `univ`) -/
example (i : ι) : i ∈ Finset.univ := by
  have h := Finset.mem_univ i
  exact h

/-! ### R6. `Finset.single_le_sum` · `(∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ ∑ x ∈ s, f x` · context
Name the summand with `(f := …)`: Lean cannot read `f` off a proof `fun i _ => …`. -/
example (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (a : ι) : f a ≤ ∑ i, f i := by
  have h := Finset.single_le_sum (f := f) (fun i _ => hf i) (Finset.mem_univ a)
  exact h

/-! ### R7. `rw [probabilityBetaReal]` · goal: `p t i` → `rexp (-t * E i) / Z t`
Under a binder (`∑ i, p t i`) write `simp only [probabilityBetaReal]` instead. -/
example (𝓒 : CanonicalEnsemble ι) (t : ℝ) (i : ι) (P : ℝ → Prop)
    (h : P (rexp (-t * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal t)) :
    P (𝓒.probabilityBetaReal t i) := by
  rw [probabilityBetaReal]
  exact h

/-! ### R8. `div_le_iff₀` · `0 < c → (a / c ≤ b ↔ a ≤ b * c)` · goal: clear the denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R9. `calc` · goal `a ≤ c` → one goal per step `a = b`, `b ≤ c`; `_` is the previous right side -/
example (a b c : ℝ) (h1 : a = b) (h2 : b ≤ c) : a ≤ c := by
  calc _ = b := ?_
    _ ≤ c := ?_
  exact h1
  exact h2

/-! ### R10. `Real.exp_add` · `rexp (x + y) = rexp x * rexp y`; `← …` merges a product of exponentials -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (rexp (x + y))) : P (rexp x * rexp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R11. `ring_nf` · closes `f u = f v` when `u` and `v` are equal as ring expressions
It normalises every subterm, also inside `rexp (…)`, and then both sides are the same text. -/
example (x y : ℝ) : rexp (-x * (y - x) + -x * x) = rexp (-x * y) := by
  ring_nf

/-! ### R12. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · context gains it -/
example (a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c := by
  have h := mul_le_mul_of_nonneg_left hbc ha
  exact h

/-! ## An excited level dies off: limits and the squeeze -/

/-! ### R13. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (a b : ℝ) (h : a < b) : 0 < b - a := by
  linarith

/-! ### R14. `tendsto_neg_atTop_atBot` · context gains `-x → -∞` as `x → ∞` -/
example (G : Prop) (g : Tendsto (fun x : ℝ => -x) atTop atBot → G) : G := by
  have h : Tendsto (fun x : ℝ => -x) atTop atBot := tendsto_neg_atTop_atBot
  exact g h

/-! ### R15. `Filter.Tendsto.atBot_mul_const` · `0 < r → f → -∞ ⇒ f · r → -∞` · context -/
example {β : Type} (l : Filter β) (f : β → ℝ) (r : ℝ) (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot := by
  have h := hf.atBot_mul_const hr
  exact h

/-! ### R16. `Real.tendsto_exp_atBot` · context gains `rexp y → 0` as `y → -∞` -/
example (G : Prop) (g : Tendsto rexp atBot (𝓝 0) → G) : G := by
  have h := Real.tendsto_exp_atBot
  exact g h

/-! ### R17. `Filter.Tendsto.comp` · `g → c` along `l'`, `f → l'` along `l` ⇒ `g ∘ f → c` along `l` · context
`(g ∘ f) x` is `g (f x)` by definition, so `exact` accepts it for `fun x => g (f x)`. -/
example {β : Type} (l : Filter β) (l' : Filter ℝ) (f : β → ℝ) (g : ℝ → ℝ) (c : ℝ)
    (hg : Tendsto g l' (𝓝 c)) (hf : Tendsto f l l') : Tendsto (fun x => g (f x)) l (𝓝 c) := by
  have h := hg.comp hf
  exact h

/-! ### R18. `tendsto_const_nhds` · a constant function tends to its value · context -/
example {β : Type} (l : Filter β) (c : ℝ) : Tendsto (fun _ : β => c) l (𝓝 c) := by
  have h : Tendsto (fun _ : β => c) l (𝓝 c) := tendsto_const_nhds
  exact h

/-! ### R19. `div_pos` · `0 < a → 0 < b → 0 < a / b` · context gains `0 < a / b` -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  have h := div_pos ha hb
  exact h

/-! ### R20. `tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh` · squeeze: goal list → `g ≤ f`, `f ≤ h`
`g ≤ f` between functions means `∀ x, g x ≤ f x` (R21). -/
example {β : Type} (l : Filter β) (f g k : β → ℝ) (a : ℝ) (hg : Tendsto g l (𝓝 a))
    (hk : Tendsto k l (𝓝 a)) (hgf : g ≤ f) (hfk : f ≤ k) : Tendsto f l (𝓝 a) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hg hk
  exact hgf
  exact hfk

/-! ### R21. `intro x` on `g ≤ f` (functions) · goal: `g ≤ f` → `g x ≤ f x`, context gains `x`
In term mode the same goal takes `fun x => …`. -/
example {β : Type} (f g : β → ℝ) (h : ∀ x, g x ≤ f x) : g ≤ f := by
  intro x
  exact h x

/-! ## The ground level: `p i = 1 - ∑ (the others)` -/

/-! ### R22. `classical` · goal unchanged; afterwards `if a = b …` and `s.erase a` typecheck for any `ι`
They need a decision procedure for `a = b` (`DecidableEq ι`); `classical` supplies one. -/
example (a : ι) (G : Prop) (g : Finset ι → G) : G := by
  classical
  exact g (Finset.univ.erase a)

/-! ### R23. `Finset.sum_div` · `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; `← …` pulls `/ a` out -/
example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) / a)) : P (∑ i, f i / a) := by
  rw [← Finset.sum_div]
  exact h

/-! ### R24. `LT.lt.ne'` · `hz.ne'` turns `hz : 0 < z` into `z ≠ 0` -/
example (z : ℝ) (hz : 0 < z) : z ≠ 0 := by
  have h := hz.ne'
  exact h

/-! ### R25. `div_self` · `a ≠ 0 → a / a = 1` · context gains the equation -/
example (a : ℝ) (ha : a ≠ 0) : a / a = 1 := by
  have h := div_self ha
  exact h

/-! ### R26. `rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h` · context: split term `a` off a sum
`Finset.add_sum_erase s f : a ∈ s → f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`; `s.erase a` is `s` without `a`. -/
example [DecidableEq ι] (f : ι → ℝ) (a : ι) (c : ℝ) (h : ∑ i, f i = c) (G : Prop)
    (g : f a + ∑ x ∈ Finset.univ.erase a, f x = c → G) : G := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
  exact g h

/-! ### R27. `simp_rw [e]` with `e : ∀ x, f x = g x` · goal: rewrites under `fun x => …`
`rw [e]` fails there: the `x` inside `fun x => f x` is bound, `rw` cannot pick it. -/
example {β : Type} (l : Filter β) (f g : β → ℝ) (L : ℝ) (e : ∀ x, f x = g x)
    (h : Tendsto (fun x => g x * 2) l (𝓝 L)) : Tendsto (fun x => f x * 2) l (𝓝 L) := by
  simp_rw [e]
  exact h

/-! ### R28. `Filter.Tendsto.sub` · `f → a`, `g → b` ⇒ `f - g → a - b` · context -/
example {β : Type} (l : Filter β) (f g : β → ℝ) (a b : ℝ) (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x - g x) l (𝓝 (a - b)) := by
  have h := hf.sub hg
  exact h

/-! ### R29. `tendsto_finsetSum` · termwise limits ⇒ limit of a finite sum · context
`tendsto_finsetSum s (fun i hi => …)`; the proof of `i ∈ s` is the second argument. -/
example {β : Type} (l : Filter β) (s : Finset ι) (F : ι → β → ℝ) (a : ι → ℝ)
    (hF : ∀ i ∈ s, Tendsto (F i) l (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, F i x) l (𝓝 (∑ i ∈ s, a i)) := by
  have h := tendsto_finsetSum s hF
  exact h

/-! ### R30. `Finset.ne_of_mem_erase` · `b ∈ s.erase a → b ≠ a` · context -/
example [DecidableEq ι] (s : Finset ι) (a b : ι) (hb : b ∈ s.erase a) : b ≠ a := by
  have h := Finset.ne_of_mem_erase hb
  exact h

/-! ### R31. `simpa using h` · simplifies `h` and the goal, then closes the goal with `h`
Here simp turns `0 * a i` into `0`, `∑ i ∈ s, 0` into `0` and `c - 0` into `c`. -/
example {β : Type} (l : Filter β) (s : Finset ι) (f : β → ℝ) (a : ι → ℝ) (c : ℝ)
    (h : Tendsto f l (𝓝 (c - ∑ i ∈ s, 0 * a i))) : Tendsto f l (𝓝 c) := by
  simpa using h

/-! ## Through `negMulLog` and the sum -/

/-! ### R32. `by_cases hi : a = b` · goal list: one goal with `hi : a = b`, one with `hi : ¬a = b` -/
example (a b : ι) (P : Prop) (h1 : a = b → P) (h2 : ¬a = b → P) : P := by
  by_cases hi : a = b
  · exact h1 hi
  · exact h2 hi

/-! ### R33. `subst hi` with `hi : a = b` (`b` a variable) · context: `b` is replaced by `a` everywhere -/
example (a b : ι) (P : ι → Prop) (hi : a = b) (hb : P b) (h : P a → P a) : P a := by
  subst hi
  exact h hb

/-! ### R34. `simp [hi]` on an `if` · goal: `if a = b then x else y` → `y` from `hi : ¬a = b`
With `hi : a = b` (or after R33, `if a = a …`) it becomes `x` instead. -/
example [DecidableEq ι] (a b : ι) (x y : ℝ) (hi : ¬a = b) (P : ℝ → Prop) (h : P y) :
    P (if a = b then x else y) := by
  simp [hi]
  exact h

/-! ### R35. `Continuous.tendsto` with `Real.continuous_negMulLog` · context gains `negMulLog y → negMulLog a` as `y → a` -/
example (a : ℝ) (G : Prop) (g : Tendsto Real.negMulLog (𝓝 a) (𝓝 (Real.negMulLog a)) → G) : G := by
  have h := Real.continuous_negMulLog.tendsto a
  exact g h

/-! ### R36. `apply_ite` · `f (if c then x else y) = if c then f x else f y` · goal -/
example (c : Prop) [Decidable c] (f : ℝ → ℝ) (x y : ℝ) (P : ℝ → Prop)
    (h : P (if c then f x else f y)) : P (f (if c then x else y)) := by
  rw [apply_ite f]
  exact h

/-! ### R37. `Real.negMulLog_zero`, `Real.negMulLog_one` · goal: `negMulLog 0` → `0`, `negMulLog 1` → `0` -/
example (P : ℝ → Prop) (h : P (0 + 0)) : P (Real.negMulLog 0 + Real.negMulLog 1) := by
  simp only [Real.negMulLog_zero, Real.negMulLog_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's limits) -/

/-! ### W1. Squeeze `0 ≤ u x ≤ rexp (-x * c)` with `c > 0`: R14 → R15, R16 → R17, R18, R20 -/
example (c : ℝ) (hc : 0 < c) (u : ℝ → ℝ) (h0 : ∀ x, 0 ≤ u x) (hu : ∀ x, u x ≤ rexp (-x * c)) :
    Tendsto u atTop (𝓝 0) := by
  have hlin : Tendsto (fun x : ℝ => -x * c) atTop atBot := tendsto_neg_atTop_atBot.atBot_mul_const hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (Real.tendsto_exp_atBot.comp hlin) h0 hu

/-! ### W2. A constant minus a finite sum of vanishing terms: R18, R28, R29, R31 -/
example (s : Finset ι) (F : ι → ℝ → ℝ) (hF : ∀ i, Tendsto (F i) atTop (𝓝 0)) :
    Tendsto (fun x => 2 - ∑ i ∈ s, F i x) atTop (𝓝 2) := by
  have h := (tendsto_const_nhds (x := (2 : ℝ)) (f := (atTop : Filter ℝ))).sub
    (tendsto_finsetSum s fun i _ => hF i)
  simpa using h

/-! ### W3. Push termwise limits through `negMulLog` and a sum: R35, R17 inside R29, then R31 with R37 -/
example (F : ι → ℝ → ℝ) (hF : ∀ i, Tendsto (F i) atTop (𝓝 0)) :
    Tendsto (fun x => ∑ i, Real.negMulLog (F i x)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ fun i _ =>
    (Real.continuous_negMulLog.tendsto _).comp (hF i)
  simpa using h

end H092Guide

/- Guide for H050 (Weak law of large numbers).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal and `k : … → G` only consumes a new hypothesis.
Part W: worked combinations on objects that are NOT the exercise's (`2 • Y`, `1 / n`, one variable).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H050Guide

open MeasureTheory ProbabilityTheory Filter Topology

/-! # Part R · Reference entries -/

/-! ## Part 1 · The mean of the sample mean (milestone `sample_mean_mean`) -/

/-! ### R1. `integral_div` · goal: `∫ a, f a / r ∂μ` → `(∫ a, f a ∂μ) / r` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (r : ℝ) (P : ℝ → Prop)
    (h : P ((∫ ω, f ω ∂μ) / r)) : P (∫ ω, f ω / r ∂μ) := by
  rw [integral_div]
  exact h

/-! ### R2. `MemLp.integrable` · `hf.integrable one_le_two : Integrable f μ` from `hf : MemLp f 2 μ`
Needs a finite measure; `IsProbabilityMeasure μ` gives `IsFiniteMeasure μ` automatically. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (G : Prop) (k : Integrable f μ → G) : G := by
  have h := hf.integrable one_le_two
  exact k h

/-! ### R3. `integral_finsetSum` · goal: integral of a finite sum → sum of the integrals
The second argument proves `∀ i ∈ s, Integrable (f i) μ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) (P : ℝ → Prop) (h : P (∑ i ∈ s, ∫ ω, f i ω ∂μ)) :
    P (∫ ω, ∑ i ∈ s, f i ω ∂μ) := by
  rw [integral_finsetSum s hf]
  exact h

/-! ### R4. `simp [hf]` on a sum of equal terms (`Finset.sum_const`, `Finset.card_range`,
`smul_eq_mul`) · goal: `∑ i ∈ Finset.range n, f i` with `hf : ∀ i, f i = c` → `↑n * c` -/
example (n : ℕ) (f : ℕ → ℝ) (c : ℝ) (hf : ∀ i, f i = c) (P : ℝ → Prop) (h : P (↑n * c)) :
    P (∑ i ∈ Finset.range n, f i) := by
  simp [hf]
  exact h

/-! ### R5. `field_simp` · clears denominators; closes `↑k * a / ↑k = a`
It needs `↑k ≠ 0` and finds it from `hk : 0 < k` in the context. -/
example (k : ℕ) (hk : 0 < k) (a : ℝ) : ↑k * a / ↑k = a := by
  field_simp

/-! ## Part 2 · The variance of the sample mean (milestone `sample_mean_variance_le`) -/

/-! ### R6. `funext ω` · goal: equation of functions → context gains `ω`, goal one value -/
example {Ω : Type} (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) : f = g := by
  funext ω
  exact h ω

/-! ### R7. `simp [Finset.sum_apply]` · goal: `(∑ i ∈ s, g i) ω` → `∑ i ∈ s, g i ω`
`∑ i ∈ s, g i` is a sum of functions (a function); applying it to `ω` sums the values. -/
example {Ω : Type} (s : Finset ℕ) (g : ℕ → Ω → ℝ) (ω : Ω) (P : ℝ → Prop)
    (h : P (∑ i ∈ s, g i ω)) : P ((∑ i ∈ s, g i) ω) := by
  simp only [Finset.sum_apply]
  exact h

/-! ### R8. `ring` · closes a field identity; division by an unknown counts: `a / b = b⁻¹ * a` -/
example (a b : ℝ) : a / b = b⁻¹ * a := by
  ring

/-! ### R9. `variance_const_mul` · `Var[fun ω => c * Y ω; μ] = c ^ 2 * Var[Y; μ]` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (Y : Ω → ℝ) (P : ℝ → Prop)
    (h : P (c ^ 2 * Var[Y; μ])) : P (Var[fun ω => c * Y ω; μ]) := by
  rw [variance_const_mul]
  exact h

/-! ### R10. `IndepFun.variance_sum` · goal: variance of a sum → sum of the variances
Hypotheses: every summand is `L²`, and the summands are pairwise independent on `s` (R11). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (Y : ℕ → Ω → ℝ)
    (hL : ∀ i ∈ s, MemLp (Y i) 2 μ) (hp : (↑s : Set ℕ).Pairwise fun i j => Y i ⟂ᵢ[μ] Y j)
    (P : ℝ → Prop) (h : P (∑ i ∈ s, Var[Y i; μ])) : P (Var[∑ i ∈ s, Y i; μ]) := by
  rw [IndepFun.variance_sum hL hp]
  exact h

/-! ### R11. `Pairwise r` → `(↑s).Pairwise r` · `intro i _ j _ hij`, then `hr hij`
`Set.Pairwise S r` is `∀ i ∈ S, ∀ j ∈ S, i ≠ j → r i j`; `Pairwise r` drops the memberships.
As a term: `fun i _ j _ hij => hr hij`. -/
example (r : ℕ → ℕ → Prop) (hr : Pairwise r) (s : Finset ℕ) : (↑s : Set ℕ).Pairwise r := by
  intro i _ j _ hij
  exact hr hij

/-! ### R12. `Finset.sum_le_sum` · goal: `∑ f ≤ ∑ g` → termwise `∀ i ∈ s, f i ≤ g i` -/
example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  apply Finset.sum_le_sum
  exact h

/-! ### R13. `exact_mod_cast` · closes a goal that is a hypothesis up to casts: `(0 : ℝ) < ↑k` from `0 < k` -/
example (k : ℕ) (hk : 0 < k) : (0 : ℝ) < k := by
  exact_mod_cast hk

/-! ### R14. `gcongr` · goal `f a ≤ f b` (same shape both sides) → `a ≤ b`, side conditions by itself
It closes the remaining `a ≤ b` itself when a hypothesis states exactly that; here `a ≤ b` is only
known through a middle term `d`, so the goal stays open. -/
example (c a b d : ℝ) (h : a ≤ d) (hd : d ≤ b) : c ^ 2 * a ≤ c ^ 2 * b := by
  gcongr
  exact h.trans hd

/-! ## Part 3 · Chebyshev's bound for the sample mean (milestone `tail_bound`) -/

/-! ### R15. `memLp_finsetSum'` · a finite sum of `L²` functions is `L²` · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (Y : ℕ → Ω → ℝ)
    (hL : ∀ i ∈ s, MemLp (Y i) 2 μ) (G : Prop) (k : MemLp (∑ i ∈ s, Y i) 2 μ → G) : G := by
  have h := memLp_finsetSum' s hL
  exact k h

/-! ### R16. `MemLp.const_mul` · `hf.const_mul c : MemLp (fun x => c * f x) p μ` · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (c : ℝ)
    (G : Prop) (k : MemLp (fun ω => c * f ω) 2 μ → G) : G := by
  have h := hf.const_mul c
  exact k h

/-! ### R17. `convert h using 1` · goal `Q b` with `h : Q a` → the difference `b = a`
`using 1` stops after one level: only the function argument of `MemLp` is compared. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (h : MemLp f 2 μ)
    (e : ∀ ω, g ω = f ω) : MemLp g 2 μ := by
  convert h using 1
  exact funext e

/-! ### R18. `meas_ge_le_variance_div_sq` (Chebyshev) · context gains the tail bound
`MemLp Y 2 μ → 0 < c → μ {ω | c ≤ |Y ω - μ[Y]|} ≤ ENNReal.ofReal (Var[Y; μ] / c ^ 2)`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : MemLp Y 2 μ) (c : ℝ) (hc : 0 < c) (G : Prop)
    (k : μ {ω | c ≤ |Y ω - μ[Y]|} ≤ ENNReal.ofReal (Var[Y; μ] / c ^ 2) → G) : G := by
  have h := meas_ge_le_variance_div_sq hY hc
  exact k h

/-! ### R19. `rw [e] at h` · context: rewrite inside a hypothesis instead of the goal -/
example (a b : ℝ) (e : a = b) (P : ℝ → Prop) (h : P a) : P b := by
  rw [e] at h
  exact h

/-! ### R20. `simp only [Real.dist_eq]` · goal: `dist x y` → `|x - y|` on `ℝ` -/
example (x y : ℝ) (P : ℝ → Prop) (h : P |x - y|) : P (dist x y) := by
  simp only [Real.dist_eq]
  exact h

/-! ### R21. `refine h.trans ?_` (`le_trans`) · goal `a ≤ c` with `h : a ≤ b` → `b ≤ c` -/
example {α : Type} [Preorder α] (a b c : α) (h : a ≤ b) (k : b ≤ c) : a ≤ c := by
  refine h.trans ?_
  exact k

/-! ### R22. `ENNReal.ofReal_le_ofReal` · goal: `ENNReal.ofReal p ≤ ENNReal.ofReal q` → `p ≤ q` -/
example (p q : ℝ) (h : p ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q := by
  apply ENNReal.ofReal_le_ofReal
  exact h

/-! ### R23. `div_div` · `a / b / c = a / (b * c)` · goal -/
example {α : Type} [DivisionCommMonoid α] (a b c : α) (P : α → Prop) (h : P (a / (b * c))) :
    P (a / b / c) := by
  rw [div_div]
  exact h

/-! ## Part 4 · The limit (theorem `weak_law`) -/

/-! ### R24. `tendstoInMeasure_iff_dist` · goal: convergence in measure → `∀ ε > 0`, tail measures `→ 0` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Z : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (h : ∀ ε, 0 < ε → Tendsto (fun n => μ {ω | ε ≤ dist (Z n ω) (g ω)}) atTop (𝓝 0)) :
    TendstoInMeasure μ Z atTop g := by
  rw [tendstoInMeasure_iff_dist]
  exact h

/-! ### R25. `rw [← ENNReal.ofReal_zero]` · goal: the target `0 : ℝ≥0∞` → `ENNReal.ofReal 0` -/
example (u : ℕ → ENNReal) (h : Tendsto u atTop (𝓝 (ENNReal.ofReal 0))) :
    Tendsto u atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  exact h

/-! ### R26. `apply ENNReal.tendsto_ofReal` · goal: a limit of `ENNReal.ofReal (v n)` → a limit of `v n` in `ℝ` -/
example (v : ℕ → ℝ) (a : ℝ) (h : Tendsto v atTop (𝓝 a)) :
    Tendsto (fun n => ENNReal.ofReal (v n)) atTop (𝓝 (ENNReal.ofReal a)) := by
  apply ENNReal.tendsto_ofReal
  exact h

/-! ### R27. `tendsto_const_div_atTop_nhds_zero_nat` · `Tendsto (fun n : ℕ => c / ↑n) atTop (𝓝 0)` · context -/
example (c : ℝ) (G : Prop) (k : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) → G) : G := by
  have h := tendsto_const_div_atTop_nhds_zero_nat c
  exact k h

/-! ### R28. `refine h.congr fun n => ?_` (`Tendsto.congr`) · goal: a limit of `v` from one of `u` → `u n = v n` -/
example (u v : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) (e : ∀ n, u n = v n) :
    Tendsto v atTop (𝓝 a) := by
  refine h.congr fun n => ?_
  exact e n

/-! ### R29. `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (squeeze) · goal list: a limit → the two bounds
Given lower `g` and upper `w` with the same limit, what is left is eventually `g ≤ f` and `f ≤ w`. -/
example (f g w : ℕ → ENNReal) (a : ENNReal) (hg : Tendsto g atTop (𝓝 a))
    (hw : Tendsto w atTop (𝓝 a)) (hgf : ∀ᶠ n in atTop, g n ≤ f n)
    (hfw : ∀ᶠ n in atTop, f n ≤ w n) : Tendsto f atTop (𝓝 a) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hw ?_ ?_
  exacts [hgf, hfw]

/-! ### R30. `tendsto_const_nhds` · closes `Tendsto (fun _ => a) l (𝓝 a)` (a constant tends to itself) -/
example (a : ENNReal) : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := by
  exact tendsto_const_nhds

/-! ### R31. `Eventually.of_forall` · goal: `∀ᶠ n in l, p n` → `∀ n, p n` -/
example (p : ℕ → Prop) (h : ∀ n, p n) : ∀ᶠ n in atTop, p n := by
  apply Eventually.of_forall
  exact h

/-! ### R32. `bot_le` · closes `⊥ ≤ x`; in `ℝ≥0∞` the bottom `⊥` is `0`, so it closes `0 ≤ x` -/
example (x : ENNReal) : 0 ≤ x := by
  exact bot_le

/-! ### R33. `eventually_ge_atTop a` · `∀ᶠ n in atTop, a ≤ n` (all large `n` are `≥ a`) · context -/
example (G : Prop) (k : (∀ᶠ n in atTop, 1 ≤ n) → G) : G := by
  have h := eventually_ge_atTop (1 : ℕ)
  exact k h

/-! ### R34. `filter_upwards [h] with n hn` · goal `∀ᶠ n in l, q n` → context gains `n`, `hn : p n`; goal `q n` -/
example (p q : ℕ → Prop) (h : ∀ᶠ n in atTop, p n) (hpq : ∀ n, p n → q n) :
    ∀ᶠ n in atTop, q n := by
  filter_upwards [h] with n hn
  exact hpq n hn

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Variance of `2 • Y` from `Var Y ≤ C`: R9, then R14 (it uses `hC` itself) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (C : ℝ)
    (hC : Var[Y; μ] ≤ C) : Var[fun ω => 2 * Y ω; μ] ≤ 2 ^ 2 * C := by
  rw [variance_const_mul]
  gcongr

/-! ### W2. Chebyshev for one variable at distance `2`: R18, R21, R22, R14 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : MemLp Y 2 μ) (C : ℝ) (hC : Var[Y; μ] ≤ C) :
    μ {ω | 2 ≤ |Y ω - μ[Y]|} ≤ ENNReal.ofReal (C / 2 ^ 2) := by
  have h := meas_ge_le_variance_div_sq hY (by norm_num : (0 : ℝ) < 2)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

/-! ### W3. An `ℝ≥0∞` limit through `ENNReal.ofReal`: R25, R26, R27 -/
example : Tendsto (fun n : ℕ => ENNReal.ofReal (3 / n)) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  apply ENNReal.tendsto_ofReal
  exact tendsto_const_div_atTop_nhds_zero_nat 3

/-! ### W4. Squeeze in `ℝ≥0∞` between `0` and a bound that holds for `n ≥ 1`: R29–R34 -/
example (f w : ℕ → ENNReal) (hw : Tendsto w atTop (𝓝 0)) (hb : ∀ n, 1 ≤ n → f n ≤ w n) :
    Tendsto f atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hb n hn

end H050Guide

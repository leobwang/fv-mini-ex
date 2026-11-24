/- Guide for H094 (Thermal quantum oscillator (Planck)).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a linear energy ladder `a·n`,
`cosh` instead of `sinh`, other series).
Infoview: `rexp` is `Real.exp`; `↑T.β` is `T.β : ℝ≥0` cast to `ℝ`; `∑'` is `tsum`.
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas

open CanonicalEnsemble Real MeasureTheory

namespace H094Guide

/-- A toy ensemble used below (not the exercise's): states `n : ℕ`, energy `a·n`, counting measure. -/
noncomputable def ladder (a : ℝ) : CanonicalEnsemble ℕ where
  energy n := a * n
  dof := 0
  μ := Measure.count
  energy_measurable := measurable_from_nat

/-! # Part R · Reference entries -/

/-! ## Exponentials: products and powers inside `rexp` -/

/-! ### R1. `Real.exp_nat_mul` · `rexp (↑n * x) = rexp x ^ n`; `rw [← Real.exp_nat_mul]` · goal -/
example (x : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (rexp (↑n * x))) : P (rexp x ^ n) := by
  rw [← Real.exp_nat_mul]
  exact h

/-! ### R2. `Real.exp_add` · `rexp (x + y) = rexp x * rexp y`; `rw [← Real.exp_add]` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (rexp (x + y))) : P (rexp x * rexp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R3. `simp only [D]` on a structure built with `where` · goal: `(D a).field` → that field's body -/
example (a : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a * ↑n)) : P ((ladder a).energy n) := by
  simp only [ladder]
  exact h

/-! ### R4. `ring_nf` · closes `f A = f B` when `A` and `B` are equal as ring expressions
`ring_nf` normalises every ring subexpression, also inside `rexp (…)`; equal normal forms close the goal. -/
example (x y : ℝ) (n : ℕ) : rexp (-(x * (↑n + y))) = rexp (-(y * x) + ↑n * -x) := by
  ring_nf

/-! ## Integrals over `ℕ` with the counting measure → sums -/

/-! ### R5. `MeasureTheory.integral_countable` · goal: `∫ x, f x ∂μ` → `∑' x, μ.real {x} • f x`
Needs `Integrable f μ`. -/
example (f : ℕ → ℝ) (hi : Integrable f Measure.count) (P : ℝ → Prop)
    (h : P (∑' n, (Measure.count : Measure ℕ).real {n} • f n)) :
    P (∫ n, f n ∂(Measure.count : Measure ℕ)) := by
  rw [integral_countable hi]
  exact h

/-! ### R6. `MeasureTheory.integrable_count_iff` · goal: `Integrable f count` → `Summable fun x => ‖f x‖` -/
example (f : ℕ → ℝ) (h : Summable fun n => ‖f n‖) : Integrable f Measure.count := by
  apply integrable_count_iff.mpr
  exact h

/-! ### R7. `simp [Measure.real]` · goal: the weight `count.real {x}` of a point → `1`, and `1 • y` → `y` -/
example (f : ℕ → ℝ) (P : ℝ → Prop) (h : P (∑' n, f n)) :
    P (∑' n, (Measure.count : Measure ℕ).real {n} • f n) := by
  simp [Measure.real]
  exact h

/-! ### R8. `Summable.abs` · context gains `Summable fun x => |f x|` from `Summable f` -/
example (f : ℕ → ℝ) (hf : Summable f) (G : Prop) (g : (Summable fun n => |f n|) → G) : G := by
  have ha := hf.abs
  exact g ha

/-! ### R9. `Real.norm_eq_abs` · `‖r‖ = |r|` for `r : ℝ` · goal -/
example (r : ℝ) (P : ℝ → Prop) (h : P |r|) : P ‖r‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! ### R10. `simpa [l] using e` · closes the goal: simplifies both the goal and `e`'s type, then matches -/
example (f : ℕ → ℝ) (ha : Summable fun n => |f n|) : Summable fun n => ‖f n‖ := by
  simpa [Real.norm_eq_abs] using ha

/-! ## Geometric series -/

/-! ### R11. `Real.exp_lt_one_iff` · `rexp x < 1 ↔ x < 0`; `.mpr` · goal `rexp x < 1` → `x < 0` -/
example (x : ℝ) (h : x < 0) : rexp x < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact h

/-! ### R12. `linarith` · closes a linear (in)equality that follows from hypotheses -/
example (x : ℝ) (hx : 0 < x) : -x < 0 := by
  linarith

/-! ### R13. `Real.exp_pos` · `0 < rexp x`; `.le` turns it into `0 ≤ rexp x` · context -/
example (x : ℝ) (G : Prop) (g : 0 ≤ rexp x → G) : G := by
  have h0 := (Real.exp_pos x).le
  exact g h0

/-! ### R14. `tsum_mul_left` · `∑' n, a * f n = a * ∑' n, f n` · goal (no summability needed) -/
example (a : ℝ) (f : ℕ → ℝ) (P : ℝ → Prop) (h : P (a * ∑' n, f n)) : P (∑' n, a * f n) := by
  rw [tsum_mul_left]
  exact h

/-! ### R15. `tsum_geometric_of_lt_one` · `0 ≤ r → r < 1 → ∑' n, r ^ n = (1 - r)⁻¹` · goal -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (P : ℝ → Prop) (h : P (1 - r)⁻¹) :
    P (∑' n : ℕ, r ^ n) := by
  rw [tsum_geometric_of_lt_one h0 h1]
  exact h

/-! ### R16. `div_eq_mul_inv` · `a / b = a * b⁻¹` · goal; `(div_eq_mul_inv a b).symm` is the reverse -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b⁻¹)) : P (a / b) := by
  rw [div_eq_mul_inv]
  exact h

/-! ## Unfolding the partition function -/

/-! ### R17. `Temperature.beta_pos` · `0 < T.val → 0 < (T.β : ℝ)` · context gains `hβ` -/
example (T : Temperature) (hT : 0 < T.val) (G : Prop) (g : 0 < (T.β : ℝ) → G) : G := by
  have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT
  exact g hβ

/-! ### R18. `CanonicalEnsemble.partitionFunction_def` · goal: `Z` → `Z_math / phaseSpaceunit ^ dof` -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (P : ℝ → Prop)
    (h : P (𝓒.mathematicalPartitionFunction T / 𝓒.phaseSpaceunit ^ 𝓒.dof)) :
    P (𝓒.partitionFunction T) := by
  rw [partitionFunction_def]
  exact h

/-! ### R19. `CanonicalEnsemble.mathematicalPartitionFunction_eq_integral` · goal: `Z_math` → an integral -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (P : ℝ → Prop)
    (h : P (∫ i, rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ)) :
    P (𝓒.mathematicalPartitionFunction T) := by
  rw [mathematicalPartitionFunction_eq_integral]
  exact h

/-! ### R20. `rw [show (D a).dof = 0 from rfl]` · goal: a field of a concrete structure → its value -/
example (a : ℝ) (P : ℕ → Prop) (h : P 0) : P (ladder a).dof := by
  rw [show (ladder a).dof = 0 from rfl]
  exact h

/-! ### R21. `pow_zero`, `div_one` · goal: `a / b ^ 0` → `a / 1` → `a` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P a) : P (a / b ^ 0) := by
  rw [pow_zero]
  rw [div_one]
  exact h

/-! ### R22. `generalize hx : e = x` · goal: every `e` → a fresh variable `x`; context gains `x`, `hx : e = x` -/
example (b a : ℝ) (P : ℝ → Prop) (h : ∀ x, P x) : P (b * a) := by
  generalize hx : b * a = x
  exact h x

/-! ### R23. `positivity` · closes `0 < e` / `0 ≤ e` for `e` built from `*`, `+`, `/`, `rexp`, … of positive atoms
An atom `a` counts as positive when `0 < a` is a hypothesis. -/
example (b a : ℝ) (hb : 0 < b) (ha : 0 < a) : 0 < b * a := by
  positivity

/-! ### R24. `summable_geometric_of_lt_one` · `0 ≤ r → r < 1 → Summable fun n => r ^ n` · context -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (G : Prop) (g : (Summable fun n : ℕ => r ^ n) → G) : G := by
  have hs := summable_geometric_of_lt_one h0 h1
  exact g hs

/-! ### R25. `Summable.mul_left` · `Summable f → Summable fun n => a * f n` · context -/
example (a : ℝ) (f : ℕ → ℝ) (hf : Summable f) (G : Prop) (g : (Summable fun n => a * f n) → G) :
    G := by
  have hs := hf.mul_left a
  exact g hs

/-! ### R26. `show G'` · goal: replaced by a definitionally equal goal (here `∂(D a).μ` → `∂Measure.count`)
`_` in `G'` stands for the part you do not want to retype. -/
example (a : ℝ) (f : ℕ → ℝ) (y : ℝ) (h : ∫ n, f n ∂Measure.count = y) : ∫ n, f n ∂(ladder a).μ = y := by
  show ∫ n, f n ∂Measure.count = _
  exact h

/-! ### R27. `simp_rw [hw]` · goal: rewrites with `hw : ∀ n, f n = g n` UNDER a binder (`∫ n, …`, `∑' n, …`)
`rw [hw]` fails there: the `n` inside `∫ n, f n` is bound, so `rw` cannot pick a value for it. -/
example (f g : ℕ → ℝ) (hw : ∀ n, f n = g n) (P : ℝ → Prop) (h : P (∫ n, g n ∂Measure.count)) :
    P (∫ n, f n ∂Measure.count) := by
  simp_rw [hw]
  exact h

/-! ### R28. `Real.sinh_eq` · `sinh x = (rexp x - rexp (-x)) / 2` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((rexp x - rexp (-x)) / 2)) : P (sinh x) := by
  rw [Real.sinh_eq]
  exact h

/-! ### R29. `simp` with `Real.exp_zero` · closes `rexp 0 = 1` -/
example : rexp 0 = 1 := by
  simp

/-! ### R30. `rw [show a = b by ring]` · goal: replace `a` by a ring-equal `b` (to match another lemma's form) -/
example (x : ℝ) (P : ℝ → Prop) (h : P (-x / 2)) : P (-(x / 2)) := by
  rw [show -(x / 2) = -x / 2 by ring]
  exact h

/-! ### R31. `generalize e = c at h₁ ⊢` · goal AND hypotheses: `e` → fresh `c`; no equation is kept -/
example (x : ℝ) (P : ℝ → Prop) (h0 : 0 < rexp x) (h : ∀ c, 0 < c → P c) : P (rexp x) := by
  generalize rexp x = c at h0 ⊢
  exact h c h0

/-! ### R32. `nlinarith` · closes (in)equalities and `≠` goals that need products of hypotheses
`nlinarith [t₁, t₂]` also uses the extra facts `tᵢ`. -/
example (a : ℝ) (h0 : 0 < a) (h1 : a < 1) : a * a < 1 := by
  nlinarith

/-! ### R33. `field_simp` · goal: clears denominators, using `≠ 0` facts in the context -/
example (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = b * c) : a / b = c / d := by
  field_simp
  exact h

/-! ### R34. `linear_combination e` · closes `L = R` when `L - R` equals `k · (lhs - rhs)` of `e` by `ring` -/
example (a b : ℝ) (h : a * b = 1) : a * b * b = b := by
  linear_combination b * h

/-! ## The mean energy -/

/-! ### R35. `CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals` · goal: `⟨E⟩` → a ratio of integrals -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (P : ℝ → Prop)
    (h : P ((∫ i, 𝓒.energy i * rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ) /
      ∫ i, rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ)) :
    P (𝓒.meanEnergy T) := by
  rw [meanEnergy_eq_ratio_of_integrals]
  exact h

/-! ### R36. `set r := e with hr` · goal: every `e` → `r`; context gains `r : ℝ := e` and `hr : r = e` -/
example (x : ℝ) (P : ℝ → Prop) (h : ∀ y, P y) : P (rexp (-x)) := by
  set r := rexp (-x) with hr
  exact h r

/-! ### R37. `abs_of_nonneg` · `0 ≤ a → |a| = a` · goal -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_nonneg ha]
  exact h

/-! ### R38. `rwa [l]` · `rw [l]`, then closes the goal with a hypothesis (`assumption`) -/
example (a : ℝ) (ha : 0 ≤ a) (h1 : a < 1) : |a| < 1 := by
  rwa [abs_of_nonneg ha]

/-! ### R39. `summable_pow_mul_geometric_of_norm_lt_one` · `‖r‖ < 1 → Summable fun n => ↑n ^ k * r ^ n`
With `k = 1`, `simpa using` removes the `^ 1`. -/
example (r : ℝ) (hr : ‖r‖ < 1) : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr

/-! ### R40. `Summable.add` · `Summable f → Summable g → Summable fun n => f n + g n` · context -/
example (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g) (G : Prop)
    (k : (Summable fun n => f n + g n) → G) : G := by
  have hs := hf.add hg
  exact k hs

/-! ### R41. `Summable.tsum_add` · `∑' n, (f n + g n) = ∑' n, f n + ∑' n, g n` (both summable) · goal -/
example (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g) (P : ℝ → Prop)
    (h : P (∑' n, f n + ∑' n, g n)) : P (∑' n, (f n + g n)) := by
  rw [hf.tsum_add hg]
  exact h

/-! ### R42. `tsum_coe_mul_geometric_of_norm_lt_one` · `‖r‖ < 1 → ∑' n, ↑n * r ^ n = r / (1 - r) ^ 2` · goal -/
example (r : ℝ) (hr : ‖r‖ < 1) (P : ℝ → Prop) (h : P (r / (1 - r) ^ 2)) :
    P (∑' n : ℕ, (n : ℝ) * r ^ n) := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
  exact h

/-! ### R43. `Real.add_one_lt_exp` · `x ≠ 0 → x + 1 < rexp x`; `hx.ne'` turns `hx : 0 < x` into `x ≠ 0`
`linarith [t]` adds the fact `t` to the hypotheses it uses. -/
example (x : ℝ) (hx : 0 < x) : 0 < rexp x - 1 := by
  linarith [Real.add_one_lt_exp hx.ne']

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The Boltzmann weight of `ladder a` as a power: R1, R3, R4 -/
example (a b : ℝ) (n : ℕ) : rexp (-b * (ladder a).energy n) = rexp (-(b * a)) ^ n := by
  rw [← Real.exp_nat_mul]
  simp only [ladder]
  ring_nf

/-! ### W2. A counting-measure integral of a geometric series: R5, R6, R7, R10, R8, R15 -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) : ∫ n, r ^ n ∂(Measure.count : Measure ℕ) = (1 - r)⁻¹ := by
  rw [integral_countable (integrable_count_iff.mpr ?_)]
  · simp [Measure.real]
    exact tsum_geometric_of_lt_one h0 h1
  · simpa [Real.norm_eq_abs] using (summable_geometric_of_lt_one h0 h1).abs

/-! ### W3. `cosh` instead of `sinh`: name `c = e^{-y}`, then the algebra is rational in `c`.
R2 + R29 for `hcc`, R31 to name `c`, R33 to clear denominators, R34 to finish. -/
example (y : ℝ) : rexp (-y) / (1 + rexp (-y) * rexp (-y)) = 1 / (2 * cosh y) := by
  rw [Real.cosh_eq]
  have hcc : rexp y * rexp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hc0 := Real.exp_pos (-y)
  have he0 := Real.exp_pos y
  generalize rexp (-y) = c at hcc hc0 ⊢
  have h1 : 1 + c * c ≠ 0 := by positivity
  have h2 : rexp y + c ≠ 0 := by positivity
  field_simp
  linear_combination hcc

/-! ### W4. Splitting a series `∑' (a·n rⁿ + b rⁿ)`: R40, R41, R14, R42, R15 -/
example (a b r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (hn : ‖r‖ < 1) :
    ∑' n : ℕ, (a * ((n : ℝ) * r ^ n) + b * r ^ n) = a * (r / (1 - r) ^ 2) + b * (1 - r)⁻¹ := by
  have hs0 : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one h0 h1
  have hs1 : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  rw [(hs1.mul_left a).tsum_add (hs0.mul_left b), tsum_mul_left, tsum_mul_left]
  rw [tsum_coe_mul_geometric_of_norm_lt_one hn, tsum_geometric_of_lt_one h0 h1]

end H094Guide

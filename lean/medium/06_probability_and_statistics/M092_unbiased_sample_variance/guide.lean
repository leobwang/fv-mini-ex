/- Guide for M092 (Unbiased sample variance).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal and `k : … → G` only consumes a new hypothesis.
Part W: worked combinations on objects that are NOT the exercise's (squares around a fixed `c`,
one variable of mean 0, a plain sum of means, a quotient by `c`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M092Guide

open MeasureTheory
open ProbabilityTheory

/-! # Part R · Reference entries -/

/-! ## Facts about `n` -/

/-! ### R1. `omega` · closes a linear goal over `ℕ`/`ℤ` from the hypotheses: `0 < k` from `1 < k` -/
example (k : ℕ) (hk : 1 < k) : 0 < k := by
  omega

/-! ### R2. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` by the shape of `e`; uses `0 < k` from the context -/
example (k : ℕ) (hk : 0 < k) : (k : ℝ) ≠ 0 := by
  positivity

/-! ### R3. `exact_mod_cast` · closes a goal that is a hypothesis up to casts: `(1 : ℝ) < ↑k` from `1 < k` -/
example (k : ℕ) (hk : 1 < k) : (1 : ℝ) < k := by
  exact_mod_cast hk

/-! ### R4. `linarith` · closes a linear (in)equality over `ℝ` that follows from the hypotheses -/
example (a b : ℝ) (h : 1 < a) (e : b = a - 1) : b ≠ 0 := by
  linarith

/-! ## The algebra: expanding a sum of squares -/

/-! ### R5. `sub_sq` · `(a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2` · goal -/
example {α : Type} [CommRing α] (a b : α) (P : α → Prop) (h : P (a ^ 2 - 2 * a * b + b ^ 2)) :
    P ((a - b) ^ 2) := by
  rw [sub_sq]
  exact h

/-! ### R6. `Finset.sum_add_distrib` · `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i` · goal -/
example {β : Type} [AddCommMonoid β] (s : Finset ℕ) (f g : ℕ → β) (P : β → Prop)
    (h : P (∑ i ∈ s, f i + ∑ i ∈ s, g i)) : P (∑ i ∈ s, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R7. `Finset.sum_sub_distrib` · `∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i` · goal -/
example {β : Type} [AddCommGroup β] (s : Finset ℕ) (f g : ℕ → β) (P : β → Prop)
    (h : P (∑ i ∈ s, f i - ∑ i ∈ s, g i)) : P (∑ i ∈ s, (f i - g i)) := by
  rw [Finset.sum_sub_distrib]
  exact h

/-! ### R8. `Finset.sum_mul` · `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; `rw [← Finset.sum_mul]` pulls a
right factor out of the sum · goal -/
example (s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P ((∑ i ∈ s, f i) * a)) :
    P (∑ i ∈ s, f i * a) := by
  rw [← Finset.sum_mul]
  exact h

/-! ### R9. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `rw [← Finset.mul_sum]` pulls a
left factor out of the sum · goal -/
example (s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (a * ∑ i ∈ s, f i)) :
    P (∑ i ∈ s, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R10. `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul` · goal: a sum of `k` copies of
`c` → `↑k * c`. `s.card` is the number of elements of `s`; `k • c` is `c + … + c` (`k` times). -/
example (k : ℕ) (c : ℝ) (P : ℝ → Prop) (h : P (↑k * c)) : P (∑ _i ∈ Finset.range k, c) := by
  rw [Finset.sum_const]
  rw [Finset.card_range]
  rw [nsmul_eq_mul]
  exact h

/-! ### R11. `field_simp` · goal: an equation with divisions → one without (multiplies out the
denominators). It needs each denominator `≠ 0`, and finds `hc : c ≠ 0` in the context. -/
example (a b c d : ℝ) (hc : c ≠ 0) (h : a + c * b = c * d) : a / c + b = d := by
  field_simp
  exact h

/-! ### R12. `ring` · closes an identity of commutative rings (here: after `field_simp`) -/
example (a b : ℝ) : (a + b) ^ 2 - 2 * a * b = a ^ 2 + b ^ 2 := by
  ring

/-! ## Naming the sum of the variables -/

/-! ### R13. `set Z : Ω → ℝ := e with hZ` · context gains `Z := e` and `hZ : Z = e`; every `e` in
the goal (and context) becomes `Z` -/
example {Ω : Type} (s : Finset ℕ) (Y : ℕ → Ω → ℝ) (P : (Ω → ℝ) → Prop) (h : P (∑ i ∈ s, Y i)) :
    P (∑ i ∈ s, Y i) := by
  set Z : Ω → ℝ := ∑ i ∈ s, Y i with hZ
  exact h

/-! ### R14. `memLp_finsetSum'` · a finite sum of `L²` functions is `L²` · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (Y : ℕ → Ω → ℝ)
    (hL : ∀ i ∈ s, MemLp (Y i) 2 μ) (G : Prop) (k : MemLp (∑ i ∈ s, Y i) 2 μ → G) : G := by
  have h := memLp_finsetSum' s hL
  exact k h

/-! ### R15. `Finset.sum_apply` · goal: `(∑ i ∈ s, g i) ω` → `∑ i ∈ s, g i ω`
`∑ i ∈ s, g i` is a sum of functions (a function); applying it to `ω` sums the values. -/
example {Ω : Type} (s : Finset ℕ) (g : ℕ → Ω → ℝ) (ω : Ω) (P : ℝ → Prop)
    (h : P (∑ i ∈ s, g i ω)) : P ((∑ i ∈ s, g i) ω) := by
  simp only [Finset.sum_apply]
  exact h

/-! ### R16. `funext ω` · goal: equation of functions → context gains `ω`, goal one value -/
example {Ω : Type} (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) : f = g := by
  funext ω
  exact h ω

/-! ## Second moments from the variance -/

/-! ### R17. `variance_eq_sub` · `MemLp Y 2 μ → Var[Y; μ] = μ[Y ^ 2] - μ[Y] ^ 2` · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : MemLp Y 2 μ) (G : Prop) (k : Var[Y; μ] = μ[Y ^ 2] - μ[Y] ^ 2 → G) : G := by
  have h := variance_eq_sub hY
  exact k h

/-! ### R18. `rw [e] at h` · context: rewrite inside a hypothesis instead of the goal -/
example (a b : ℝ) (e : a = b) (P : ℝ → Prop) (h : P a) : P b := by
  rw [e] at h
  exact h

/-! ### R19. `Pi.pow_apply` · `(Y ^ 2) ω = Y ω ^ 2`; `simp only [Pi.pow_apply] at h` turns
`μ[Y ^ 2]` into the integral of `fun ω => Y ω ^ 2` · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (r : ℝ) (h : μ[Y ^ 2] = r) :
    ∫ ω, Y ω ^ 2 ∂μ = r := by
  simp only [Pi.pow_apply] at h
  exact h

/-! ## Expectations of sums -/

/-! ### R20. `integral_finsetSum` · goal: integral of a finite sum → sum of the integrals
The second argument proves `∀ i ∈ s, Integrable (f i) μ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) (P : ℝ → Prop) (h : P (∑ i ∈ s, ∫ ω, f i ω ∂μ)) :
    P (∫ ω, ∑ i ∈ s, f i ω ∂μ) := by
  rw [integral_finsetSum s hf]
  exact h

/-! ### R21. `MemLp.integrable` · `hf.integrable one_le_two : Integrable f μ` from `hf : MemLp f 2 μ`
Needs a finite measure; `IsProbabilityMeasure μ` gives it automatically. · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (G : Prop) (k : Integrable f μ → G) : G := by
  have h := hf.integrable one_le_two
  exact k h

/-! ## Independence: the variance of the sum -/

/-! ### R22. `IndepFun.variance_sum` · goal: variance of a sum → sum of the variances
Hypotheses: every summand is `L²`, and the summands are pairwise independent on `s` (R23). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (Y : ℕ → Ω → ℝ)
    (hL : ∀ i ∈ s, MemLp (Y i) 2 μ) (hp : (↑s : Set ℕ).Pairwise fun i j => Y i ⟂ᵢ[μ] Y j)
    (P : ℝ → Prop) (h : P (∑ i ∈ s, Var[Y i; μ])) : P (Var[∑ i ∈ s, Y i; μ]) := by
  rw [IndepFun.variance_sum hL hp]
  exact h

/-! ### R23. `Pairwise r` → `(↑s).Pairwise r` · `intro i _ j _ hij`, then `hr hij`
`Set.Pairwise S r` is `∀ i ∈ S, ∀ j ∈ S, i ≠ j → r i j`; `Pairwise r` drops the memberships.
As a term: `fun i _ j _ hij => hr hij`. -/
example (r : ℕ → ℕ → Prop) (hr : Pairwise r) (s : Finset ℕ) : (↑s : Set ℕ).Pairwise r := by
  intro i _ j _ hij
  exact hr hij

/-! ## The final computation -/

/-! ### R24. `integral_div` · goal: `∫ a, f a / r ∂μ` → `(∫ a, f a ∂μ) / r` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (r : ℝ) (P : ℝ → Prop)
    (h : P ((∫ ω, f ω ∂μ) / r)) : P (∫ ω, f ω / r ∂μ) := by
  rw [integral_div]
  exact h

/-! ### R25. `integral_sub` · goal list: `∫ (f - g)` → `∫ f - ∫ g`, plus side goals
`Integrable f μ` and `Integrable g μ` (rewriting without the two proofs as arguments). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P ((∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω - g ω ∂μ) := by
  rw [integral_sub]
  exact h
  exact hf
  exact hg

/-! ### R26. `MemLp.integrable_sq` · `hf.integrable_sq : Integrable (fun ω => f ω ^ 2) μ` · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (G : Prop)
    (k : Integrable (fun ω => f ω ^ 2) μ → G) : G := by
  have h := hf.integrable_sq
  exact k h

/-! ### R27. `integrable_finsetSum` · a finite sum of integrable functions is integrable · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) (G : Prop)
    (k : Integrable (fun ω => ∑ i ∈ s, f i ω) μ → G) : G := by
  have h := integrable_finsetSum s hf
  exact k h

/-! ### R28. `Integrable.div_const` · `hf.div_const c : Integrable (fun ω => f ω / c) μ` · context -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)
    (G : Prop) (k : Integrable (fun ω => f ω / c) μ → G) : G := by
  have h := hf.div_const c
  exact k h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Squares around a fixed `c`: R5 → R7, R6 → R8, R9 → R10, then `ring` -/
example (k : ℕ) (x : ℕ → ℝ) (c : ℝ) :
    ∑ i ∈ Finset.range k, (x i - c) ^ 2
      = ∑ i ∈ Finset.range k, x i ^ 2 - 2 * c * ∑ i ∈ Finset.range k, x i + k * c ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-! ### W2. One variable of mean 0 and variance 1 has `E[Y²] = 1`: R17, R18, R19, R4 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : MemLp Y 2 μ) (h0 : μ[Y] = 0) (h1 : Var[Y; μ] = 1) : ∫ ω, Y ω ^ 2 ∂μ = 1 := by
  have h := variance_eq_sub hY
  rw [h1, h0] at h
  simp only [Pi.pow_apply] at h
  linarith

/-! ### W3. The mean of `∑ i < k, Y i` when each `E[Y i] = a`: R20 with R21, then `simp [ha]` (R10) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ)
    (Y : ℕ → Ω → ℝ) (a : ℝ) (hL : ∀ i, MemLp (Y i) 2 μ) (ha : ∀ i, μ[Y i] = a) :
    ∫ ω, ∑ i ∈ Finset.range k, Y i ω ∂μ = k * a := by
  rw [integral_finsetSum _ (fun i _ => (hL i).integrable one_le_two)]
  simp [ha]

/-! ### W4. `rw` with `integral_div` and `integral_sub`: R24, R25, R24. The main goal closes by
itself (`rw` tries `rfl`); the two `Integrable` side goals are left, closed by R26 and R28 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y Z : Ω → ℝ)
    (hY : MemLp Y 2 μ) (hZ : Integrable Z μ) (c : ℝ) :
    ∫ ω, (Y ω ^ 2 - Z ω / c) / 2 ∂μ = ((∫ ω, Y ω ^ 2 ∂μ) - (∫ ω, Z ω ∂μ) / c) / 2 := by
  rw [integral_div, integral_sub, integral_div]
  · exact hY.integrable_sq
  · exact hZ.div_const c

end M092Guide

/- Guide for H053 (Variance of the binomial distribution).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact from a lemma use `have h := …`, so the context gains `h` and you can read
off exactly what the lemma produced.
Part W: worked combinations on objects that are NOT the exercise's (other sums, another measure).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H053Guide

/-! # Part R · Reference entries -/

/-! ## From an integral against `Bin(n, p)` to a finite sum -/

/-! ### R1. `integral_binomial` · goal: `∫ x, f x ∂Bin(n, q)` → a finite sum over `Finset.Iic n`
`∫ x, f x ∂Bin(n, q) = ∑ k ∈ Finset.Iic n, (↑(n.choose k) * ↑q ^ k * (1 - ↑q) ^ (n - k)) • f k` -/
example (n : ℕ) (q : unitInterval) (f : ℕ → ℝ) (P : ℝ → Prop)
    (h : P (∑ k ∈ Finset.Iic n, ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) • f k)) :
    P (∫ x, f x ∂binomial n q) := by
  rw [integral_binomial]
  exact h

/-! ### R2. `Nat.range_succ_eq_Iic` · `Finset.range (n + 1) = Finset.Iic n`; used right to left
`Finset.Iic n = {0, …, n}` and `Finset.range (n + 1) = {0, …, n}` are the same set; the `range` form is
the one `Finset.sum_range_succ'` and `add_pow` speak about. -/
example (n : ℕ) (g : ℕ → ℝ) (P : ℝ → Prop) (h : P (∑ k ∈ Finset.range (n + 1), g k)) :
    P (∑ k ∈ Finset.Iic n, g k) := by
  rw [← Nat.range_succ_eq_Iic]
  exact h

/-! ## Case split on `n` and peeling terms off a sum -/

/-! ### R3. `match n with | 0 => … | 1 => … | m + 2 => …` · goal list: one goal per shape of `n`
The tactic `match n with` followed by the three alternatives (each with its own tactic block) gives
the same three goals, proved in place. `refine match … ?_` below shows them one after another. -/
example (P : ℕ → Prop) (h0 : P 0) (h1 : P 1) (h2 : ∀ m, P (m + 2)) (n : ℕ) : P n := by
  refine match n with | 0 => ?_ | 1 => ?_ | m + 2 => ?_
  exacts [h0, h1, h2 _]

/-! ### R4. `Finset.sum_range_succ'` · goal: peel the FIRST term `f 0` off a sum over `range (n + 1)`
`∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0` (the remaining terms are reindexed). -/
example (n : ℕ) (f : ℕ → ℝ) (P : ℝ → Prop)
    (h : P (∑ k ∈ Finset.range n, f (k + 1) + f 0)) : P (∑ k ∈ Finset.range (n + 1), f k) := by
  rw [Finset.sum_range_succ']
  exact h

/-! ### R5. `Finset.sum_range_succ` · goal: peel the LAST term `f n` off a sum over `range (n + 1)`
`∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`. With `simp [Finset.sum_range_succ]` a sum over
`range (1 + 1)` unrolls completely (`range 0` is empty). -/
example (n : ℕ) (f : ℕ → ℝ) (P : ℝ → Prop)
    (h : P (∑ k ∈ Finset.range n, f k + f n)) : P (∑ k ∈ Finset.range (n + 1), f k) := by
  rw [Finset.sum_range_succ]
  exact h

/-! ### R6. `smul_eq_mul` · goal: `a • b` → `a * b` (`ℝ` acting on itself by scalars is `*`) -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R7. `Nat.cast_zero`, `Nat.cast_one` · goal: `↑0` → `0`, `↑1` → `1` (`ℕ` numerals cast to `ℝ`) -/
example (P : ℝ → Prop) (h : P (0 + 1)) : P (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) := by
  simp only [Nat.cast_zero, Nat.cast_one]
  exact h

/-! ### R8. `zero_mul`, `mul_zero`, `sub_self`, `zero_add`, `add_zero` · goal: a vanishing term disappears
`0 * a = 0`, `a * 0 = 0`, `a - a = 0`, `0 + a = a`, `a + 0 = a`. -/
example (s c : ℝ) (P : ℝ → Prop) (h : P s) : P (0 + s + c * (0 * (0 - 1)) + c * (1 * (1 - 1))) := by
  simp only [zero_mul, mul_zero, sub_self, zero_add, add_zero]
  exact h

/-! ## One term at a time: casts and binomial coefficients -/

/-! ### R9. `intro k hk` · goal `∀ k ∈ s, Q k` → context gains `k` and `hk : k ∈ s`
`∀ k ∈ s, Q k` is notation for `∀ k, k ∈ s → Q k`. Write `intro k _` when `hk` is not needed. -/
example (s : Finset ℕ) (Q : ℕ → Prop) (h : ∀ k, Q k) : ∀ k ∈ s, Q k := by
  intro k hk
  exact h k

/-! ### R10. `Nat.add_one_mul_choose_eq` · context gains the absorption identity, in `ℕ`
`(a + 1) * a.choose b = (a + 1).choose (b + 1) * (b + 1)`, i.e. `(a+1)·C(a,b) = (b+1)·C(a+1,b+1)`. -/
example (a b : ℕ) : (a + 1) * a.choose b = (a + 1).choose (b + 1) * (b + 1) := by
  have h := Nat.add_one_mul_choose_eq a b
  exact h

/-! ### R11. `exact_mod_cast e` · closes a goal in `ℝ` with a fact `e` in `ℕ` that differs only by casts -/
example (x y z w : ℕ) (e : x * y = z * w) : (x : ℝ) * y = z * w := by
  exact_mod_cast e

/-! ### R12. `rw [show a + 1 - (b + 1) = a - b by omega]` · goal: rewrite with an `ℕ` fact proved on the spot
`-` on `ℕ` is truncated (`2 - 5 = 0`), so `ring` cannot simplify it; `omega` (linear arithmetic over
`ℕ`/`ℤ`) can. -/
example (a b : ℕ) (P : ℕ → Prop) (h : P (a - b)) : P (a + 1 - (b + 1)) := by
  rw [show a + 1 - (b + 1) = a - b by omega]
  exact h

/-! ### R13. `push_cast at h ⊢` · context and goal: casts pushed to the leaves, `↑(m + 2)` → `↑m + 2` -/
example (m k : ℕ) (x : ℝ) (h : ((m + 2 : ℕ) : ℝ) = k) : ((m + 2 : ℕ) : ℝ) * x = k * x := by
  push_cast at h ⊢
  rw [h]

/-! ### R14. `linear_combination e * h` · closes `L = R` when `L - R = e * (lhs h - rhs h)` by `ring`
`e` may be any expression; several facts: `linear_combination e₁ * h₁ + e₂ * h₂`. -/
example (a b c x : ℝ) (h : a * b = c) : x * a * b + 1 = x * c + 1 := by
  linear_combination x * h

/-! ## The whole sum: rewrite each term, pull out a constant, binomial theorem -/

/-! ### R15. `Finset.sum_congr rfl key` · goal: every term of a sum rewritten by `key`
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`. `rfl` says the index set
stays `s`; `key : ∀ k ∈ s, f k = …` is the per-term identity (here `f k = 2 * g k`). -/
example (s : Finset ℕ) (f g : ℕ → ℝ) (key : ∀ k ∈ s, f k = 2 * g k) (P : ℝ → Prop)
    (h : P (∑ k ∈ s, 2 * g k)) : P (∑ k ∈ s, f k) := by
  rw [Finset.sum_congr rfl key]
  exact h

/-! ### R16. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; right to left pulls `a` out -/
example (s : Finset ℕ) (a : ℝ) (f : ℕ → ℝ) (P : ℝ → Prop) (h : P (a * ∑ i ∈ s, f i)) :
    P (∑ i ∈ s, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R17. `add_pow` · binomial theorem; right to left folds the sum into `(x + y) ^ m`
`(x + y) ^ m = ∑ k ∈ range (m + 1), x ^ k * y ^ (m - k) * ↑(m.choose k)`. The summand must have exactly
this shape (order of the three factors included). -/
example (x y : ℝ) (m : ℕ) (P : ℝ → Prop) (h : P ((x + y) ^ m)) :
    P (∑ k ∈ Finset.range (m + 1), x ^ k * y ^ (m - k) * (m.choose k : ℝ)) := by
  rw [← add_pow]
  exact h

/-! ### R18. `add_sub_cancel` · `a + (b - a) = b` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P b) : P (a + (b - a)) := by
  rw [add_sub_cancel]
  exact h

/-! ### R19. `one_pow`, `mul_one` · `1 ^ m = 1`, `a * 1 = a` · goal -/
example (a : ℝ) (m : ℕ) (P : ℝ → Prop) (h : P a) : P (a * 1 ^ m) := by
  rw [one_pow]
  rw [mul_one]
  exact h

/-! ## Integrals: integrability and linearity -/

/-! ### R20. `integrable_binomial f` · context gains `Integrable f Bin(n, q)`, for EVERY `f`
`Bin(n, q)` lives on the finite set `{0, …, n}`, so no condition on `f` is needed. -/
example (n : ℕ) (q : unitInterval) (f : ℕ → ℝ) : Integrable f (binomial n q) := by
  have h := integrable_binomial (n := n) (p := q) f
  exact h

/-! ### R21. `integral_add hf hg` · `∫ (f + g) = ∫ f + ∫ g`; right to left merges two integrals
`hf : Integrable f μ`, `hg : Integrable g μ`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ x, f x + g x ∂μ)) :
    P (∫ x, f x ∂μ + ∫ x, g x ∂μ) := by
  rw [← integral_add hf hg]
  exact h

/-! ### R22. `congr 1` · goal `∫ x, F x ∂μ = ∫ x, G x ∂μ` → `F = G` (the integrands) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (F G : Ω → ℝ) (h : ∀ x, F x = G x) :
    ∫ x, F x ∂μ = ∫ x, G x ∂μ := by
  congr 1
  exact funext h

/-! ### R23. `funext k` · goal `F = G` (functions) → `F k = G k` for a new `k` -/
example (F G : ℕ → ℝ) (h : ∀ k, F k = G k) : F = G := by
  funext k
  exact h k

/-! ## Variance -/

/-! ### R24. `hf.aestronglyMeasurable` · from `hf : Integrable f μ`, context gains
`AEStronglyMeasurable f μ` (`f` agrees a.e. with a limit of simple functions: a measurability
side condition, always true on `ℕ`). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) :
    AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable
  exact h

/-! ### R25. `(memLp_two_iff_integrable_sq hm).2 hsq` · context gains `MemLp f 2 μ` (`f ∈ L²(μ)`)
`memLp_two_iff_integrable_sq hm : MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ`, given
`hm : AEStronglyMeasurable f μ`; `.2` is the `←` direction of the `↔`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hm : AEStronglyMeasurable f μ)
    (hsq : Integrable (fun x => f x ^ 2) μ) : MemLp f 2 μ := by
  have h := (memLp_two_iff_integrable_sq hm).2 hsq
  exact h

/-! ### R26. `variance_eq_sub hX` · goal: `Var[X; μ]` → `E[X²] - E[X]²` (needs `hX : MemLp X 2 μ` and a
probability measure `μ`). The square appears as `(X ^ 2) x`, the square of the FUNCTION applied to `x`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (P : ℝ → Prop) (h : P (∫ x, (X ^ 2) x ∂μ - (∫ x, X x ∂μ) ^ 2)) :
    P (Var[X; μ]) := by
  rw [variance_eq_sub hX]
  exact h

/-! ### R27. `simp only [Pi.pow_apply]` · goal: `(f ^ 2) x` → `f x ^ 2`
`Pi.pow_apply : (f ^ a) i = f i ^ a`; `simp` also β-reduces, so `((fun k => ↑k) ^ 2) x` becomes `↑x ^ 2`. -/
example (f : ℕ → ℝ) (x : ℕ) (P : ℝ → Prop) (h : P (f x ^ 2)) : P ((f ^ 2) x) := by
  simp only [Pi.pow_apply]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Peel two terms with R4 twice, then clean the vanishing ones with R6–R8 -/
example (m : ℕ) (c : ℕ → ℝ) :
    ∑ k ∈ Finset.range (m + 2), c k • ((k : ℝ) * ((k : ℝ) - 1)) =
      ∑ k ∈ Finset.range m, c (k + 1 + 1) * (((k + 1 + 1 : ℕ) : ℝ) * (((k + 1 + 1 : ℕ) : ℝ) - 1)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [smul_eq_mul, Nat.cast_zero, zero_add, Nat.cast_one, zero_mul, sub_self, mul_zero,
    add_zero]

/-! ### W2. A constant times a binomial sum: R16 then R17 (here with `x + y = 2`) -/
example (m : ℕ) (a : ℝ) :
    ∑ k ∈ Finset.range (m + 1), a * ((1 : ℝ) ^ k * 1 ^ (m - k) * (m.choose k : ℝ)) = a * 2 ^ m := by
  rw [← Finset.mul_sum]
  rw [← add_pow]
  norm_num

/-! ### W3. The tactic `match`: three alternatives, each with its own tactic block (R3) -/
example (n : ℕ) : n = 0 ∨ n = 1 ∨ 2 ≤ n := by
  match n with
    | 0 => left; rfl
    | 1 => right; left; rfl
    | m + 2 => right; right; omega

/-! ### W4. An `ℕ` fact moved to `ℝ` (R11), then used in a `linear_combination` (R14) -/
example (a b : ℕ) (x : ℝ) (e : 2 * a = b + 3) : (b : ℝ) * x + 3 * x = 2 * a * x := by
  have h : (2 : ℝ) * a = b + 3 := by exact_mod_cast e
  linear_combination -x * h

/-! ### W5. The variance pipeline on another measure: R25, R26, R27, then the moments -/
example (μ : Measure ℕ) [IsProbabilityMeasure μ] (hint : ∀ f : ℕ → ℝ, Integrable f μ)
    (h1 : ∫ k, (k : ℝ) ∂μ = 2) (h2 : ∫ k, (k : ℝ) ^ 2 ∂μ = 5) :
    Var[fun k : ℕ => (k : ℝ); μ] = 1 := by
  have hX : MemLp (fun k : ℕ => (k : ℝ)) 2 μ :=
    (memLp_two_iff_integrable_sq (hint _).aestronglyMeasurable).2 (hint _)
  rw [variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [h1, h2]
  norm_num

end H053Guide

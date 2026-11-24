/- Guide for M168 (Bloch states are delocalised).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on states that are NOT the exercise's (arbitrary coefficients `c n`,
other phases).
Assumed: Lean basics.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace M168Guide

/-! # Part R · Reference entries -/

/-! ## Unfolding the state and pushing the inner product inside -/

/-! ### R1. `simp only [TightBindingChain.energyEigenstate]` · goal: the name → its body, a sum
`↑↑k` is `k` cast twice: subtype element → `ℝ` → `ℂ`; `↑↑n` is `n : Fin T.N` → `ℕ` → `ℂ`. -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (P : T.HilbertSpace → Prop)
    (h : P (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • localizedState n)) :
    P (T.energyEigenstate k) := by
  simp only [TightBindingChain.energyEigenstate]
  exact h

/-! ### R2. `inner_sum` · `⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫` · goal: sum on the right moves out -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type} (s : Finset ι)
    (f : ι → E) (x : E) (P : ℂ → Prop) (h : P (∑ i ∈ s, ⟪x, f i⟫_ℂ)) :
    P ⟪x, ∑ i ∈ s, f i⟫_ℂ := by
  simp only [inner_sum]
  exact h

/-! ### R3. `inner_smul_right` · `⟪x, r • y⟫ = r * ⟪x, y⟫` · goal: scalar on the right moves out as is -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (r : ℂ)
    (P : ℂ → Prop) (h : P (r * ⟪x, y⟫_ℂ)) : P ⟪x, r • y⟫_ℂ := by
  simp only [inner_smul_right]
  exact h

/-! ### R4. `localizedState_orthonormal_eq_ite` · `⟪|m⟩, |n⟩⟫ = if m = n then 1 else 0` · goal -/
example (T : TightBindingChain) (m n : Fin T.N) (P : ℂ → Prop) (h : P (if m = n then 1 else 0)) :
    P ⟪localizedState m, localizedState n⟫_ℂ := by
  simp only [localizedState_orthonormal_eq_ite]
  exact h

/-! ## Collapsing the sum with the `if` -/

/-! ### R5. `mul_ite` · `a * (if p then b else c) = if p then a * b else a * c` · goal -/
example {α : Type} [Mul α] (p : Prop) [Decidable p] (a b c : α) (P : α → Prop)
    (h : P (if p then a * b else a * c)) : P (a * if p then b else c) := by
  simp only [mul_ite]
  exact h

/-! ### R6. `mul_one`, `mul_zero` · `a * 1 = a`, `a * 0 = 0` · goal -/
example {α : Type} [MulZeroOneClass α] (p : Prop) [Decidable p] (a : α) (P : α → Prop)
    (h : P (if p then a else 0)) : P (if p then a * 1 else a * 0) := by
  simp only [mul_one, mul_zero]
  exact h

/-! ### R7. `Finset.sum_ite_eq` · `∑ j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i else 0`
The `if` must test `i = j` with the summation variable `j` on the RIGHT (R8 handles `j = i`). -/
example {ι β : Type} [DecidableEq ι] [AddCommMonoid β] (s : Finset ι) (i : ι) (f : ι → β)
    (P : β → Prop) (h : P (if i ∈ s then f i else 0)) :
    P (∑ j ∈ s, if i = j then f j else 0) := by
  simp only [Finset.sum_ite_eq]
  exact h

/-! ### R8. `Finset.sum_ite_eq'` · `∑ j ∈ s, (if j = i then f j else 0) = if i ∈ s then f i else 0`
The mirror of R7: summation variable `j` on the LEFT of `=`. -/
example {ι β : Type} [DecidableEq ι] [AddCommMonoid β] (s : Finset ι) (i : ι) (f : ι → β)
    (P : β → Prop) (h : P (if i ∈ s then f i else 0)) :
    P (∑ j ∈ s, if j = i then f j else 0) := by
  simp only [Finset.sum_ite_eq']
  exact h

/-! ### R9. `Finset.mem_univ`, `if_true` · `i ∈ Finset.univ` is `True`; `if True then a else b = a` -/
example {ι β : Type} [Fintype ι] [DecidableEq ι] (i : ι) (a b : β) (P : β → Prop) (h : P a) :
    P (if i ∈ Finset.univ then a else b) := by
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ## The modulus of a phase -/

/-! ### R10. `Complex.norm_exp` · `‖exp z‖ = Real.exp z.re` · goal: a complex norm → a real exponential -/
example (z : ℂ) (P : ℝ → Prop) (h : P (Real.exp z.re)) : P ‖Complex.exp z‖ := by
  simp only [Complex.norm_exp]
  exact h

/-! ### R11. `Complex.mul_re` · `(z * w).re = z.re * w.re - z.im * w.im` · goal -/
example (z w : ℂ) (P : ℝ → Prop) (h : P (z.re * w.re - z.im * w.im)) : P (z * w).re := by
  simp only [Complex.mul_re]
  exact h

/-! ### R12. `simp` · goal: `.re` of `I` times real casts → `0`
`simp` uses `Complex.mul_re`, `Complex.mul_im`, `Complex.I_re` (`= 0`), `Complex.I_im` (`= 1`),
`Complex.ofReal_re`, `Complex.ofReal_im` (`= 0`), `Complex.natCast_re`, `Complex.natCast_im`. -/
example (x y : ℝ) (m : ℕ) (P : ℝ → Prop) (h : P 0) :
    P (Complex.I * ↑x * ↑m * ↑y).re := by
  simp
  exact h

/-! ### R13. `Real.exp_zero` · `Real.exp 0 = 1` · goal -/
example (P : ℝ → Prop) (h : P 1) : P (Real.exp 0) := by
  simp only [Real.exp_zero]
  exact h

/-! ## Inner products with the sum and the scalar on the LEFT -/

/-! ### R14. `sum_inner` · `⟪∑ i ∈ s, f i, x⟫ = ∑ i ∈ s, ⟪f i, x⟫` · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type} (s : Finset ι)
    (f : ι → E) (x : E) (P : ℂ → Prop) (h : P (∑ i ∈ s, ⟪f i, x⟫_ℂ)) :
    P ⟪∑ i ∈ s, f i, x⟫_ℂ := by
  simp only [sum_inner]
  exact h

/-! ### R15. `inner_smul_left` · `⟪r • x, y⟫ = conj r * ⟪x, y⟫` · goal: scalar on the left leaves conjugated
`(starRingEnd ℂ) r` is how Lean prints the complex conjugate `conj r`. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (r : ℂ)
    (P : ℂ → Prop) (h : P ((starRingEnd ℂ) r * ⟪x, y⟫_ℂ)) : P ⟪r • x, y⟫_ℂ := by
  simp only [inner_smul_left]
  exact h

/-! ## Conjugates and exponentials -/

/-! ### R16. `← Complex.exp_conj` · `conj (exp z) → exp (conj z)` (the lemma read right to left) -/
example (z : ℂ) (P : ℂ → Prop) (h : P (Complex.exp ((starRingEnd ℂ) z))) :
    P ((starRingEnd ℂ) (Complex.exp z)) := by
  simp only [← Complex.exp_conj]
  exact h

/-! ### R17. `map_mul` · `conj (a * b) = conj a * conj b` (holds for any multiplicative map) -/
example (a b : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)) :
    P ((starRingEnd ℂ) (a * b)) := by
  simp only [map_mul]
  exact h

/-! ### R18. `Complex.conj_I` · `conj I = -I` · goal -/
example (P : ℂ → Prop) (h : P (-Complex.I)) : P ((starRingEnd ℂ) Complex.I) := by
  simp only [Complex.conj_I]
  exact h

/-! ### R19. `Complex.conj_ofReal`, `map_natCast` · `conj ↑r = ↑r` for `r : ℝ`, `conj ↑m = ↑m` for `m : ℕ` -/
example (r : ℝ) (m : ℕ) (P : ℂ → Prop) (h : P (↑r * ↑m)) :
    P ((starRingEnd ℂ) ↑r * (starRingEnd ℂ) ↑m) := by
  simp only [Complex.conj_ofReal, map_natCast]
  exact h

/-! ### R20. `neg_mul` · `-a * b = -(a * b)` · goal: pulls a minus sign out of a product -/
example {α : Type} [Mul α] [HasDistribNeg α] (a b : α) (P : α → Prop) (h : P (-(a * b))) :
    P (-a * b) := by
  simp only [neg_mul]
  exact h

/-! ### R21. `← Complex.exp_add` · `exp x * exp y → exp (x + y)` (the lemma read right to left) -/
example (x y : ℂ) (P : ℂ → Prop) (h : P (Complex.exp (x + y))) :
    P (Complex.exp x * Complex.exp y) := by
  simp only [← Complex.exp_add]
  exact h

/-! ### R22. `neg_add_cancel`, `add_neg_cancel` · `-a + a = 0`, `a + -a = 0` · goal
Which one you need depends on whether `simp` left `conj (exp z) * exp z` or `exp z * conj (exp z)`. -/
example {α : Type} [AddGroup α] (a : α) (P : α → Prop) (h : P 0) : P (-a + a) := by
  simp only [neg_add_cancel]
  exact h

example {α : Type} [AddGroup α] (a : α) (P : α → Prop) (h : P 0) : P (a + -a) := by
  simp only [add_neg_cancel]
  exact h

/-! ### R23. `Complex.exp_zero` · `exp 0 = 1` · goal -/
example (P : ℂ → Prop) (h : P 1) : P (Complex.exp 0) := by
  simp only [Complex.exp_zero]
  exact h

/-! ## Counting: a sum of ones over `Fin N` -/

/-! ### R24. `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul` · goal
`∑ _x ∈ s, b = s.card • b`; `Finset.univ.card = Fintype.card α`; `Fintype.card (Fin N) = N`;
`N • a = ↑N * a` (`•` here is repeated addition by a natural number). -/
example (N : ℕ) (P : ℂ → Prop) (h : P (↑N * 1)) : P (∑ _x : Fin N, (1 : ℂ)) := by
  simp only [Finset.sum_const]
  simp only [Finset.card_univ]
  simp only [Fintype.card_fin]
  simp only [nsmul_eq_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's states) -/

/-! ### W1. Any state `∑ n, c n • |n⟩` has amplitude `c m` on site `m`: R2, R3, R4, then R5, R6, R7, R9 -/
example (T : TightBindingChain) (c : Fin T.N → ℂ) (m : Fin T.N) :
    ⟪localizedState m, ∑ n, c n • localizedState n⟫_ℂ = c m := by
  simp only [inner_sum, inner_smul_right, localizedState_orthonormal_eq_ite]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ### W2. Its squared norm is `∑ n, c n * conj (c n)`. Pull the LEFT sum out first (R14), then
R15, R2, R3, R4: the `if` reads `x = x_1` with the inner summation variable on the right, so R7 fits. -/
example (T : TightBindingChain) (c : Fin T.N → ℂ) :
    ⟪∑ n, c n • localizedState n, ∑ n, c n • localizedState n⟫_ℂ =
      ∑ n, c n * (starRingEnd ℂ) (c n) := by
  simp only [sum_inner]
  simp only [inner_smul_left, inner_sum, inner_smul_right, localizedState_orthonormal_eq_ite]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ### W3. W2 with every lemma in ONE `simp only`: `simp` pulls the RIGHT sum out first, the `if`
comes out as `x_1 = x` (summation variable on the left), and R8 is the lemma that collapses it. -/
example (T : TightBindingChain) (c : Fin T.N → ℂ) :
    ⟪∑ n, c n • localizedState n, ∑ n, c n • localizedState n⟫_ℂ =
      ∑ n, c n * (starRingEnd ℂ) (c n) := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    localizedState_orthonormal_eq_ite]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ### W4. A phase `exp (x * I)` with the `I` on the other side still has modulus 1: R10, R12, R13 -/
example (x : ℝ) : ‖Complex.exp (↑x * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp]

/-! ### W5. `conj (exp (I x)) * exp (I x) = 1`: R16, R17, R18, R19, R20, R21, R22, R23 -/
example (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * ↑x)) * Complex.exp (Complex.I * ↑x) = 1 := by
  simp only [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  simp only [← Complex.exp_add]
  simp only [neg_add_cancel, Complex.exp_zero]

end M168Guide

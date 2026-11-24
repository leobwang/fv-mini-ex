/- Guide for H099 (Tight-binding sum rules).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders, in the order the skeletons use them. Put the cursor before and after the step to see
the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (cube roots of unity, other sums).
Assumed: Lean basics (E001–E033).
-/
import Physlib.CondensedMatter.TightBindingChain.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

open CondensedMatter

namespace H099Guide

/-! # Part R · Reference entries -/

/-! ## `sum_cos`, step 1: the case `N = 0` -/

/-! ### R1. `rcases Nat.eq_zero_or_pos N with rfl | hN` · goal list: one goal with `N` replaced
by `0`, one goal with `hN : 0 < N` in the context -/
example (P : ℕ → Prop) (h0 : P 0) (hpos : ∀ N, 0 < N → P N) (N : ℕ) : P N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact h0
  · exact hpos N hN

/-! ### R2. `Fin.sum_univ_zero` · goal: a sum over `Fin 0` (no terms) → `0`; `simp` uses it -/
example {β : Type} [AddCommMonoid β] (f : Fin 0 → β) (P : β → Prop) (h : P 0) : P (∑ i, f i) := by
  rw [Fin.sum_univ_zero]
  exact h

/-! ## `sum_cos`, step 2: the root of unity `ζ` -/

/-! ### R3. `h.ne'` (`LT.lt.ne'`) · `0 < n → n ≠ 0` · context gains the `≠` fact -/
example (n : ℕ) (h : 0 < n) (G : Prop) (g : n ≠ 0 → G) : G := by
  have hn : n ≠ 0 := h.ne'
  exact g hn

/-! ### R4. `Complex.isPrimitiveRoot_exp n hn` · context gains
`IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) n`: `exp (2πi/n)` is a primitive
`n`-th root of unity -/
example (n : ℕ) (hn : n ≠ 0) (G : Prop)
    (g : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n → G) : G := by
  have hω := Complex.isPrimitiveRoot_exp n hn
  exact g hω

/-! ### R5. `set z := e with hz` · context gains `z := e` and `hz : z = e`; every `e` in the goal
and the context becomes `z` -/
example {M : Type} [Monoid M] (a : M) (j : ℕ) (P : M → Prop) (h : P (a ^ j)) : P (a ^ j) := by
  set z := a ^ j with hz
  exact h

/-! ### R6. `IsPrimitiveRoot.pow_eq_one_iff_dvd` · `IsPrimitiveRoot ζ k → (ζ ^ l = 1 ↔ k ∣ l)` · goal -/
example {M : Type} [CommMonoid M] (ζ : M) (k l : ℕ) (hζ : IsPrimitiveRoot ζ k) (P : Prop)
    (h : k ∣ l → P) : ζ ^ l = 1 → P := by
  rw [hζ.pow_eq_one_iff_dvd l]
  exact h

/-! ### R7. `pow_mul` · `a ^ (m * n) = (a ^ m) ^ n`; right to left `rw [← pow_mul]` merges powers · goal -/
example {M : Type} [Monoid M] (a : M) (m n : ℕ) (P : M → Prop) (h : P (a ^ (m * n))) :
    P ((a ^ m) ^ n) := by
  rw [← pow_mul]
  exact h

/-! ### R8. `mul_comm m n` · `m * n = n * m` (with arguments: only that product) · goal -/
example (m n : ℕ) (P : ℕ → Prop) (h : P (n * m)) : P (m * n) := by
  rw [mul_comm m n]
  exact h

/-! ### R9. `IsPrimitiveRoot.pow_eq_one` · `IsPrimitiveRoot ζ k → ζ ^ k = 1` · goal -/
example {M : Type} [CommMonoid M] (ζ : M) (k : ℕ) (hζ : IsPrimitiveRoot ζ k) (P : M → Prop)
    (h : P 1) : P (ζ ^ k) := by
  rw [hζ.pow_eq_one]
  exact h

/-! ### R10. `one_pow` · `1 ^ n = 1` · goal -/
example {M : Type} [Monoid M] (n : ℕ) (P : M → Prop) (h : P 1) : P (1 ^ n) := by
  rw [one_pow]
  exact h

/-! ## `sum_cos`, step 3: the geometric sum vanishes -/

/-! ### R11. `geom_sum_mul x n` · `(∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1` · context -/
example {α : Type} [Ring α] (x : α) (n : ℕ) (G : Prop)
    (g : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 → G) : G := by
  have h := geom_sum_mul x n
  exact g h

/-! ### R12. `rw [sub_self] at h` · `a - a = 0` · context: the hypothesis `h` is rewritten -/
example {α : Type} [Ring α] (a s : α) (h : s = a - a) : s = 0 := by
  rw [sub_self] at h
  exact h

/-! ### R13. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0` (no zero divisors) · context -/
example {α : Type} [MulZeroClass α] [NoZeroDivisors α] (a b : α) (h : a * b = 0) (G : Prop)
    (g : a = 0 ∨ b = 0 → G) : G := by
  have h' := mul_eq_zero.mp h
  exact g h'

/-! ### R14. `Or.resolve_right` · `A ∨ B → ¬B → A` · closes the goal `A` -/
example (A B : Prop) (h : A ∨ B) (hB : ¬B) : A := by
  exact h.resolve_right hB

/-! ### R15. `sub_ne_zero` · `a - b ≠ 0 ↔ a ≠ b` · goal -/
example {α : Type} [AddGroup α] (a b : α) (h : a ≠ b) : a - b ≠ 0 := by
  rw [sub_ne_zero]
  exact h

/-! ## `sum_cos`, step 4: cosines as real parts, then factor out the phase -/

/-! ### R16. `Complex.re_sum` · `(∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re` · goal -/
example {ι : Type} (s : Finset ι) (f : ι → ℂ) (P : ℝ → Prop) (h : P (∑ i ∈ s, (f i).re)) :
    P (∑ i ∈ s, f i).re := by
  rw [Complex.re_sum]
  exact h

/-! ### R17. `Complex.exp_ofReal_mul_I_re` · `(Complex.exp (↑x * Complex.I)).re = Real.cos x` ·
goal; under `∑` use `simp only`, since `rw` cannot rewrite under a binder -/
example {ι : Type} (s : Finset ι) (θ : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ s, Real.cos (θ i))) :
    P (∑ i ∈ s, (Complex.exp (↑(θ i) * Complex.I)).re) := by
  simp only [Complex.exp_ofReal_mul_I_re]
  exact h

/-! ### R18. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal; right to left
(`← Finset.mul_sum`) it pulls a constant factor out of the sum -/
example {ι α : Type} [NonUnitalNonAssocSemiring α] (s : Finset ι) (a : α) (f : ι → α)
    (P : α → Prop) (h : P (∑ i ∈ s, a * f i)) : P (a * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R19. `Fin.sum_univ_eq_sum_range f n` · `∑ i : Fin n, f ↑i = ∑ i ∈ Finset.range n, f i` ·
goal; right to left (give `f` explicitly) it turns a `range` sum into a `Fin` sum -/
example {β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) (P : β → Prop)
    (h : P (∑ i : Fin n, f ↑i)) : P (∑ i ∈ Finset.range n, f i) := by
  rw [← Fin.sum_univ_eq_sum_range f n]
  exact h

/-! ### R20. `congr 1` · goal `f a = f b` → `a = b` (peels one function application) -/
example (z w : ℂ) (h : z + 0 = w) : z.re = w.re := by
  congr 1
  simpa using h

/-- The same on `Complex.exp`: the goal becomes the equation of the exponents. (Had `z = w` itself
been a hypothesis, `congr 1` would have closed the new goal on its own.) -/
example (z w : ℂ) (h : z + 0 = w) : Complex.exp z = Complex.exp w := by
  congr 1
  simpa using h

/-! ### R21. `refine Finset.sum_congr rfl fun i _ => ?_` · goal: equal sums → equal summands;
context gains `i` and `x✝ : i ∈ Finset.univ` -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M) (hfg : ∀ i, f i = g i) :
    ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hfg i

/-! ### R22. `Complex.exp_nat_mul` · `Complex.exp (↑n * x) = Complex.exp x ^ n`; right to left
a power of an exponential becomes one exponential · goal -/
example (x : ℂ) (n : ℕ) (P : ℂ → Prop) (h : P (Complex.exp (↑n * x))) :
    P (Complex.exp x ^ n) := by
  rw [← Complex.exp_nat_mul]
  exact h

/-! ### R23. `Complex.exp_add` · `Complex.exp (x + y) = Complex.exp x * Complex.exp y`; right to
left a product of exponentials becomes one · goal -/
example (x y : ℂ) (P : ℂ → Prop) (h : P (Complex.exp (x + y))) :
    P (Complex.exp x * Complex.exp y) := by
  rw [← Complex.exp_add]
  exact h

/-! ### R24. `push_cast` · goal: casts `↑` are pushed inward to the atoms (`↑(x * y - z)` →
`↑x * ↑y - ↑z`, and a cast of a cast of `n : ℕ` → one cast) -/
example (x y : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P (↑x * ↑y - ↑n)) :
    P (↑(x * y - (n : ℝ))) := by
  push_cast
  exact h

/-! ### R25. `simp` · closes `(a * 0).re = 0` (it uses `mul_zero`, then `Complex.zero_re`) -/
example (a : ℂ) : (a * 0).re = 0 := by
  simp

/-! ## `ka_eq`: the wavenumber times the lattice spacing -/

/-! ### R26. `TightBindingChain.a_pos` · `T.a_pos : 0 < T.a` (a field of the structure) ·
context gains `T.a ≠ 0` with R3 -/
example (T : TightBindingChain) (G : Prop) (g : T.a ≠ 0 → G) : G := by
  have ha := T.a_pos.ne'
  exact g ha

/-! ### R27. `simp only [d]` on a definition whose value is `⟨x, proof⟩` in a subtype · goal:
`↑d` (the value, `Subtype.val d`) → `x` -/
noncomputable def half : {x : ℝ | 0 < x} := ⟨1 / 2, by norm_num⟩
example (P : ℝ → Prop) (h : P (1 / 2)) : P (half : ℝ) := by
  simp only [half]
  exact h

/-! ### R28. `field_simp` · goal: clears every denominator whose `≠ 0` fact is in the context,
then normalises; often closes the goal -/
example (a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : x / (a * b) * a = x / b := by
  field_simp

/-! ## `band_sum_rule`: `N ∤ 1`, unfold, split the sum -/

/-! ### R29. `Nat.not_dvd_of_pos_of_lt` · `0 < m → m < n → ¬ n ∣ m` · goal list: two side goals;
in a term write `Nat.not_dvd_of_pos_of_lt one_pos (by omega)` (`one_pos : 0 < 1`, `two_pos : 0 < 2`) -/
example (N : ℕ) (hN : 4 ≤ N) : ¬ N ∣ 3 := by
  apply Nat.not_dvd_of_pos_of_lt
  · norm_num
  · omega

/-! ### R30. `simp only [Nat.cast_one, mul_one] at h` · context: `↑1` (the natural `1` cast to `ℝ`)
→ `1`, then `x * 1` → `x` inside `h` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (x * ((1 : ℕ) : ℝ))) : P x := by
  simp only [Nat.cast_one, mul_one] at h
  exact h

/-! ### R31. `TightBindingChain.energyEigenvalue` · `T.energyEigenvalue k = T.E0 - 2 * T.t *
Real.cos (↑k * T.a)` · goal; `simp only` unfolds it, also under `∑` -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (P : ℝ → Prop)
    (h : P (T.E0 - 2 * T.t * Real.cos (↑k * T.a))) : P (T.energyEigenvalue k) := by
  simp only [TightBindingChain.energyEigenvalue]
  exact h

/-! ### R32. `simp only [hfg]` with `hfg : ∀ i, f i = g i` · goal: rewrites under `∑`, where `rw`
fails ("Did not find an occurrence of the pattern f ?i": the `i` under `∑` is a bound variable) -/
example (N : ℕ) (f g : Fin N → ℝ) (hfg : ∀ i, f i = g i) (P : ℝ → Prop)
    (h : P (∑ i, Real.cos (g i))) : P (∑ i, Real.cos (f i)) := by
  simp only [hfg]
  exact h

/-! ### R33. `Finset.sum_sub_distrib` · `∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i` · goal -/
example {ι α : Type} [AddCommGroup α] (s : Finset ι) (f g : ι → α) (P : α → Prop)
    (h : P (∑ i ∈ s, f i - ∑ i ∈ s, g i)) : P (∑ i ∈ s, (f i - g i)) := by
  rw [Finset.sum_sub_distrib]
  exact h

/-! ### R34. `Finset.sum_const` · `∑ _i ∈ s, c = s.card • c` (`•`: `n • c = c + ⋯ + c`) · goal -/
example {ι α : Type} [AddCommMonoid α] (s : Finset ι) (c : α) (P : α → Prop)
    (h : P (s.card • c)) : P (∑ _i ∈ s, c) := by
  rw [Finset.sum_const]
  exact h

/-! ### R35. `Finset.card_univ`, `Fintype.card_fin` · `Finset.univ.card = Fintype.card ι`,
`Fintype.card (Fin n) = n` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Finset.univ : Finset (Fin n)).card := by
  rw [Finset.card_univ]
  rw [Fintype.card_fin]
  exact h

/-! ### R36. `nsmul_eq_mul` · `n • a = ↑n * a` · goal -/
example (n : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (↑n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ## `band_second_moment`: one term at a time -/

/-! ### R37. `rw [show A = B by ring]` · goal: rewrite with an identity proved on the spot;
`A` must appear literally in the goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (x ^ 2 * y ^ 2)) : P ((x * y) ^ 2) := by
  rw [show (x * y) ^ 2 = x ^ 2 * y ^ 2 by ring]
  exact h

/-! ### R38. `Real.cos_sq x` · `Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P (1 / 2 + Real.cos (2 * x) / 2)) : P (Real.cos x ^ 2) := by
  rw [Real.cos_sq]
  exact h

/-! ### R39. `ring_nf` · closes a goal whose two sides differ inside a function argument: it
normalises every subterm, so `Real.cos (2 * (a / b))` and `Real.cos (a * 2 / b)` get the same
normal form. `ring` treats `Real.cos (…)` as an opaque atom, fails, and prints "Try this: ring_nf" -/
example (a b c : ℝ) : c * Real.cos (2 * (a / b)) = Real.cos (a * 2 / b) * c := by
  ring_nf

/-! ### R40. `Finset.sum_add_distrib` · `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i` · goal -/
example {ι α : Type} [AddCommMonoid α] (s : Finset ι) (f g : ι → α) (P : α → Prop)
    (h : P (∑ i ∈ s, f i + ∑ i ∈ s, g i)) : P (∑ i ∈ s, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A cube root of unity `z ≠ 1` has `1 + z + z²  = 0`: R11, R12, R13, R14, R15 -/
example (z : ℂ) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) : ∑ i ∈ Finset.range 3, z ^ i = 0 := by
  have h := geom_sum_mul z 3
  rw [hz3, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz1)

/-! ### W2. Split a sum of `c - 3 f(i)` over `Fin n`: R33, R34, R35, R36, R18 right to left -/
example (n : ℕ) (c : ℝ) (f : Fin n → ℝ) (hf : ∑ i, f i = 0) :
    ∑ i, (c - 3 * f i) = n * c := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hf]
  ring

/-! ### W3. A cosine as the real part of a phase times a power: R16, R17, then R22, R23 -/
example (θ φ : ℝ) (n : ℕ) :
    Real.cos (φ + n * θ) = (Complex.exp (φ * Complex.I) * Complex.exp (θ * Complex.I) ^ n).re := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

end H099Guide

/- Guide for H084 (The quantum Fourier transform is unitary).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`π i / 3`, other sums).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix Complex

namespace H084Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · exponentials as powers -/

/-! ### R1. `Complex.exp_nat_mul` · `exp (↑n * x) = exp x ^ n`; right to left: `rw [← Complex.exp_nat_mul]` · goal -/
example (x : ℂ) (n : ℕ) (P : ℂ → Prop) (h : P (Complex.exp (n * x))) : P (Complex.exp x ^ n) := by
  rw [← Complex.exp_nat_mul]
  exact h

/-! ### R2. `congr 1` · goal `f a = f b` → `a = b` (strip one function application on both sides)
`congr 1` closes the new goal by itself when it is `rfl` or a hypothesis. -/
example (a b : ℂ) (h : b = a) : Complex.exp a = Complex.exp b := by
  congr 1
  exact h.symm

/-! ### R3. `ring` · closes field identities: `x / y` is `x * y⁻¹`, and `y⁻¹` is one more unknown -/
example (a b c d : ℂ) : a * b * c / d = c * (a * b / d) := by ring

/-! ## Part 2 · the conjugate of the root -/

/-! ### R4. `Complex.exp_conj` · `exp (conj x) = conj (exp x)`; right to left moves `conj` inside · goal -/
example (x : ℂ) (P : ℂ → Prop) (h : P (Complex.exp ((starRingEnd ℂ) x))) :
    P ((starRingEnd ℂ) (Complex.exp x)) := by
  rw [← Complex.exp_conj]
  exact h

/-! ### R5. `Complex.exp_neg` · `exp (-x) = (exp x)⁻¹`; right to left · goal -/
example (x : ℂ) (P : ℂ → Prop) (h : P (Complex.exp (-x))) : P (Complex.exp x)⁻¹ := by
  rw [← Complex.exp_neg]
  exact h

/-! ### R6. `map_div₀` · `f (a / b) = f a / f b` for `f = starRingEnd ℂ` (any field map) · goal -/
example (a b : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a / (starRingEnd ℂ) b)) :
    P ((starRingEnd ℂ) (a / b)) := by
  rw [map_div₀]
  exact h

/-! ### R7. `map_mul` · `f (a * b) = f a * f b` · goal -/
example (a b : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)) :
    P ((starRingEnd ℂ) (a * b)) := by
  rw [map_mul]
  exact h

/-! ### R8. `map_ofNat` · `f 2 = 2` (any numeral literal `≥ 2`) · goal -/
example (P : ℂ → Prop) (h : P 2) : P ((starRingEnd ℂ) 2) := by
  simp only [map_ofNat]
  exact h

/-! ### R9. `Complex.conj_ofReal` · `conj ↑r = ↑r` for a real `r` cast to `ℂ` · goal -/
example (r : ℝ) (P : ℂ → Prop) (h : P ↑r) : P ((starRingEnd ℂ) ↑r) := by
  rw [Complex.conj_ofReal]
  exact h

/-! ### R10. `Complex.conj_I` · `conj I = -I` · goal -/
example (P : ℂ → Prop) (h : P (-I)) : P ((starRingEnd ℂ) I) := by
  rw [Complex.conj_I]
  exact h

/-! ### R11. `map_natCast` · `f ↑n = ↑n` for a natural number `n` cast into `ℂ` · goal -/
example (n : ℕ) (P : ℂ → Prop) (h : P ↑n) : P ((starRingEnd ℂ) ↑n) := by
  rw [map_natCast]
  exact h

/-! ## Part 3 · orthogonality -/

/-! ### R12. `rintro rfl` · goal `n ≠ 0` (that is `n = 0 → False`) → `False`, with `n` replaced by `0` -/
example (n : ℕ) (P : ℕ → Prop) (hP : P n) (h0 : ¬P 0) : n ≠ 0 := by
  rintro rfl
  exact h0 hP

/-! ### R13. `Fin.elim0` · `j : Fin 0` cannot exist, so `j.elim0` proves any goal · goal closed -/
example (C : Prop) (j : Fin 0) : C := by
  exact j.elim0

/-! ### R14. `set x := e with hx` · context gains `x := e` and `hx : x = e`; goal: every `e` → `x` -/
example (a b : ℂ) (P : ℂ → Prop) (h : ∀ y, y = Complex.exp a → P (y * b)) :
    P (Complex.exp a * b) := by
  set ζ := Complex.exp a with hζ
  exact h ζ hζ

/-! ### R15. `Complex.isPrimitiveRoot_exp` · `n ≠ 0 → IsPrimitiveRoot (exp (2πi / n)) n` · context -/
example (n : ℕ) (hn : n ≠ 0) (G : Prop)
    (g : IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / n)) n → G) : G := by
  have hprim := Complex.isPrimitiveRoot_exp n hn
  exact g hprim

/-! ### R16. `IsPrimitiveRoot.ne_zero` · `IsPrimitiveRoot ζ k → k ≠ 0 → ζ ≠ 0` · context -/
example (ζ : ℂ) (k : ℕ) (hprim : IsPrimitiveRoot ζ k) (hk : k ≠ 0) (G : Prop) (g : ζ ≠ 0 → G) :
    G := by
  have hne := hprim.ne_zero hk
  exact g hne

/-! ### R17. `simp only [h]` with `h : ∀ m, f m = g m` · goal: rewrites under `∑ k, …`, where `rw` cannot -/
example (n : ℕ) (f g : ℕ → ℂ) (h : ∀ m, f m = g m) (P : ℂ → Prop) (hP : P (∑ k : Fin n, g k)) :
    P (∑ k : Fin n, f k) := by
  simp only [h]
  exact hP

/-! ### R18. `map_pow` · `f (a ^ n) = f a ^ n` · goal -/
example (a : ℂ) (n : ℕ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a ^ n)) :
    P ((starRingEnd ℂ) (a ^ n)) := by
  rw [map_pow]
  exact h

/-! ### R19. `mul_pow` · `(a * b) ^ n = a ^ n * b ^ n` · goal -/
example {M : Type} [CommMonoid M] (a b : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * b ^ n)) :
    P ((a * b) ^ n) := by
  rw [mul_pow]
  exact h

/-! ### R20. `pow_mul` · `a ^ (m * n) = (a ^ m) ^ n`; both directions · goal -/
example {M : Type} [Monoid M] (a : M) (m n : ℕ) (P : M → Prop) (h : P ((a ^ m) ^ n)) :
    P (a ^ (m * n)) := by
  rw [pow_mul]
  exact h

example {M : Type} [Monoid M] (a : M) (m n : ℕ) (P : M → Prop) (h : P (a ^ (m * n))) :
    P ((a ^ m) ^ n) := by
  rw [← pow_mul]
  exact h

/-! ### R21. `Fin.sum_univ_eq_sum_range f n` · `∑ i : Fin n, f ↑i = ∑ i ∈ range n, f i` · goal
Give `f` explicitly (`fun k => …`): Lean cannot guess it from the summand. -/
example {β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) (P : β → Prop)
    (h : P (∑ i ∈ Finset.range n, f i)) : P (∑ i : Fin n, f i) := by
  rw [Fin.sum_univ_eq_sum_range f n]
  exact h

/-! ### R22. `split_ifs with h` · goal with `if c then a else b` → two goals, `h : c` and `h : ¬c` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (ha : c → P a) (hb : ¬c → P b) :
    P (if c then a else b) := by
  split_ifs with h
  exacts [ha h, hb h]

/-! ### R23. `subst h` · `h : a = b` with `b` a variable: context loses `b` and `h`; goal: `b` → `a` -/
example {α : Type} (a b : α) (P : α → α → Prop) (h : a = b) (hp : P a a) : P a b := by
  subst h
  exact hp

/-! ### R24. `inv_pow` · `a⁻¹ ^ n = (a ^ n)⁻¹` · goal -/
example {α : Type} [DivisionMonoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n)⁻¹) :
    P (a⁻¹ ^ n) := by
  rw [inv_pow]
  exact h

/-! ### R25. `pow_ne_zero` · `a ≠ 0 → a ^ n ≠ 0` · context -/
example (a : ℂ) (n : ℕ) (ha : a ≠ 0) (G : Prop) (g : a ^ n ≠ 0 → G) : G := by
  have han := pow_ne_zero n ha
  exact g han

/-! ### R26. `mul_inv_cancel₀` · `a ≠ 0 → a * a⁻¹ = 1` · goal -/
example {G : Type} [GroupWithZero G] (a : G) (ha : a ≠ 0) (P : G → Prop) (h : P 1) :
    P (a * a⁻¹) := by
  rw [mul_inv_cancel₀ ha]
  exact h

/-! ### R27. `Finset.sum_const` · `∑ _x ∈ s, c = s.card • c` (a sum of a constant) · goal -/
example {ι β : Type} [AddCommMonoid β] (s : Finset ι) (c : β) (P : β → Prop) (h : P (s.card • c)) :
    P (∑ _x ∈ s, c) := by
  rw [Finset.sum_const]
  exact h

/-! ### R28. `Finset.card_range` · `(range n).card = n` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Finset.range n).card := by
  rw [Finset.card_range]
  exact h

/-! ### R29. `nsmul_eq_mul` · `n • a = ↑n * a` (repeated addition → multiplication by the cast) · goal -/
example (n : ℕ) (a : ℂ) (P : ℂ → Prop) (h : P (↑n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R30. `mul_comm a b` · `a * b = b * a`, only for this `a` and `b` · goal -/
example (a b c : ℕ) (P : ℕ → ℕ → Prop) (h : P (b * a) (c * a)) : P (a * b) (c * a) := by
  rw [mul_comm a b]
  exact h

/-! ### R31. `IsPrimitiveRoot.pow_eq_one` · `IsPrimitiveRoot ζ k → ζ ^ k = 1` · goal -/
example (ζ : ℂ) (k : ℕ) (hprim : IsPrimitiveRoot ζ k) (P : ℂ → Prop) (h : P 1) : P (ζ ^ k) := by
  rw [hprim.pow_eq_one]
  exact h

/-! ### R32. `apply h` with `h : ¬A` · goal `False` → `A` (`¬A` is `A → False`) -/
example (A B : Prop) (h : ¬A) (hb : B → A) (b : B) : False := by
  apply h
  exact hb b

/-! ### R33. `rw [e] at h` · context: rewrites the hypothesis `h`, goal unchanged -/
example (a : ℂ) (n : ℕ) (Q : ℂ → Prop) (h : Q (a⁻¹ ^ n)) : Q (a ^ n)⁻¹ := by
  rw [inv_pow] at h
  exact h

/-! ### R34. `mul_inv_eq_one₀` · `b ≠ 0 → (a * b⁻¹ = 1 ↔ a = b)`; `.mp` uses `→` · context -/
example {G : Type} [GroupWithZero G] (a b : G) (hb : b ≠ 0) (h : a * b⁻¹ = 1) (Q : Prop)
    (g : a = b → Q) : Q := by
  have hab := (mul_inv_eq_one₀ hb).mp h
  exact g hab

/-! ### R35. `IsPrimitiveRoot.pow_inj` · `i < k → j < k → ζ ^ i = ζ ^ j → i = j` · context -/
example (ζ : ℂ) (k i j : ℕ) (hprim : IsPrimitiveRoot ζ k) (hi : i < k) (hj : j < k)
    (H : ζ ^ i = ζ ^ j) (Q : Prop) (g : i = j → Q) : Q := by
  have hij := hprim.pow_inj hi hj H
  exact g hij

/-! ### R36. `Fin.isLt` · `(i : Fin n) → ↑i < n` · context -/
example (n : ℕ) (i : Fin n) (Q : Prop) (g : (i : ℕ) < n → Q) : Q := by
  have hi := i.isLt
  exact g hi

/-! ### R37. `Fin.ext` · `↑a = ↑b → a = b` (equal values ⇒ equal elements of `Fin n`) · goal -/
example (n : ℕ) (a b : Fin n) (h : (a : ℕ) = b) : a = b := by
  apply Fin.ext
  exact h

/-! ### R38. `geom_sum_eq` · `x ≠ 1 → ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1)` · goal -/
example {K : Type} [DivisionRing K] (x : K) (hx : x ≠ 1) (n : ℕ) (P : K → Prop)
    (h : P ((x ^ n - 1) / (x - 1))) : P (∑ i ∈ Finset.range n, x ^ i) := by
  rw [geom_sum_eq hx]
  exact h

/-! ### R39. `sub_self` · `a - a = 0` · goal -/
example {α : Type} [AddGroup α] (a : α) (P : α → Prop) (h : P 0) : P (a - a) := by
  rw [sub_self]
  exact h

/-! ### R40. `zero_div` · `0 / a = 0` · goal -/
example {K : Type} [DivisionRing K] (a : K) (P : K → Prop) (h : P 0) : P (0 / a) := by
  rw [zero_div]
  exact h

/-! ## Part 4 · unitarity -/

/-! ### R41. `Matrix.mem_unitaryGroup_iff` · goal: `M ∈ unitaryGroup n ℂ` → `M * star M = 1` -/
example {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (h : M * star M = 1) :
    M ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact h

/-! ### R42. `Fin.pos`, `.ne'` · `(i : Fin n) → 0 < n`; `h.ne' : n ≠ 0` for `h : 0 < n` · context -/
example (n : ℕ) (i : Fin n) (Q : Prop) (g : n ≠ 0 → Q) : Q := by
  have hn := (Fin.pos i).ne'
  exact g hn

/-! ### R43. `Nat.cast_ne_zero` · `(↑n : ℂ) ≠ 0 ↔ n ≠ 0`; `.mpr` uses `←` · context -/
example (n : ℕ) (hn : n ≠ 0) (Q : Prop) (g : (n : ℂ) ≠ 0 → Q) : Q := by
  have hc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  exact g hc

/-! ### R44. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) (i k : n) (P : ℂ → Prop)
    (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R45. `Matrix.star_apply` · `star M i j = star (M j i)` (conjugate transpose, entrywise) · goal -/
example {n : Type} (M : Matrix n n ℂ) (i j : n) (P : ℂ → Prop) (h : P (star (M j i))) :
    P (star M i j) := by
  rw [Matrix.star_apply]
  exact h

/-! ### R46. `Matrix.of_apply` · `Matrix.of f i j = f i j` (a matrix given by a formula) · goal -/
example {n : Type} (f : n → n → ℂ) (i j : n) (P : ℂ → Prop) (h : P (f i j)) :
    P (Matrix.of f i j) := by
  rw [Matrix.of_apply]
  exact h

/-! ### R47. `star_mul'` · `star (a * b) = star a * star b` (commutative `*`) · goal -/
example (a b : ℂ) (P : ℂ → Prop) (h : P (star a * star b)) : P (star (a * b)) := by
  rw [star_mul']
  exact h

/-! ### R48. `RCLike.star_def` · `star = starRingEnd ℂ` on `ℂ`: `star a` → `(starRingEnd ℂ) a` · goal -/
example (a : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a)) : P (star a) := by
  simp only [RCLike.star_def]
  exact h

/-! ### R49. `map_inv₀` · `f a⁻¹ = (f a)⁻¹` · goal -/
example (a : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a)⁻¹) : P ((starRingEnd ℂ) a⁻¹) := by
  rw [map_inv₀]
  exact h

/-! ### R50. `trans b` · goal list: `a = c` → `a = b` and `b = c` -/
example (a b c : ℂ) (h1 : a = b) (h2 : b = c) : a = c := by
  trans b
  exacts [h1, h2]

/-! ### R51. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal -/
example {ι : Type} (s : Finset ι) (f : ι → ℂ) (a : ℂ) (P : ℂ → Prop)
    (h : P (∑ i ∈ s, a * f i)) : P (a * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R52. `Finset.sum_congr rfl` · goal: equal sums → equal summands -/
example {ι : Type} (s : Finset ι) (f g : ι → ℂ) (h : ∀ x ∈ s, f x = g x) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  apply Finset.sum_congr rfl
  exact h

/-! ### R53. `Complex.ofReal_pow` · `↑(x ^ n) = ↑x ^ n`; right to left moves `^` inside the cast · goal -/
example (x : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P ↑(x ^ n)) : P (↑x ^ n) := by
  rw [← Complex.ofReal_pow]
  exact h

/-! ### R54. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · goal -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! ### R55. `Nat.cast_nonneg` · `0 ≤ (↑n : ℝ)` · context -/
example (n : ℕ) (Q : Prop) (g : 0 ≤ (n : ℝ) → Q) : Q := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  exact g hn

/-! ### R56. `Matrix.one_apply` · `(1 : Matrix n n ℂ) i j = if i = j then 1 else 0` · goal -/
example {n : Type} [DecidableEq n] (i j : n) (P : ℂ → Prop) (h : P (if i = j then 1 else 0)) :
    P ((1 : Matrix n n ℂ) i j) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R57. `push_cast` · goal: a cast of a cast `((↑n : ℝ) : ℂ)` → `(↑n : ℂ)` -/
example (n : ℕ) (P : ℂ → Prop) (h : P (n : ℂ)) : P ((n : ℝ) : ℂ) := by
  push_cast
  exact h

/-! ### R58. `inv_mul_cancel₀` · `a ≠ 0 → a⁻¹ * a = 1` · goal -/
example {G : Type} [GroupWithZero G] (a : G) (ha : a ≠ 0) (P : G → Prop) (h : P 1) :
    P (a⁻¹ * a) := by
  rw [inv_mul_cancel₀ ha]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An exponential as a power: R1, then R2 and R3 -/
example (m : ℕ) : Complex.exp (Real.pi * I * m / 3) = Complex.exp (Real.pi * I / 3) ^ m := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-! ### W2. Conjugate of `exp (π i / 3)`: R4, R5, R2, then `simp` (R6–R11) and R3 -/
example : starRingEnd ℂ (Complex.exp (Real.pi * I / 3)) = (Complex.exp (Real.pi * I / 3))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal, map_div₀, map_ofNat]
  ring

/-! ### W3. Under `∑`, a sum of powers `r ^ ↑k` over `Fin n` → over `range n` (R21, explicit `f`) -/
example (r : ℂ) (n : ℕ) : ∑ k : Fin n, r ^ (k : ℕ) = ∑ k ∈ Finset.range n, r ^ k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => r ^ k)]

/-! ### W4. A geometric sum of an `n`-th root of unity `r ≠ 1` vanishes: R38, R39, R40 -/
example (r : ℂ) (n : ℕ) (hrn : r ^ n = 1) (hr1 : r ≠ 1) : ∑ i ∈ Finset.range n, r ^ i = 0 := by
  rw [geom_sum_eq hr1]
  rw [hrn]
  rw [sub_self]
  rw [zero_div]

/-! ### W5. When `r = 1`, the geometric sum counts: `simp` applies R27, R28, R29 -/
example (n : ℕ) : ∑ i ∈ Finset.range n, (1 : ℂ) ^ i = n := by
  simp

/-! ### W6. Pull a constant out of a sum: R51 on the right side, R52, then `ring` per summand
In the exercise the target right side is not given, so `trans (c ^ 2 * ∑ …)` (R50) writes it first. -/
example (s : Finset ℕ) (c : ℂ) (f g : ℕ → ℂ) :
    ∑ k ∈ s, c * f k * (c * g k) = c ^ 2 * ∑ k ∈ s, f k * g k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ### W7. `(√x)⁻¹ ^ 2 = x⁻¹` in `ℂ`: R24, R53, R54 -/
example (x : ℝ) (hx : 0 ≤ x) : ((Real.sqrt x : ℂ)⁻¹) ^ 2 = (x : ℂ)⁻¹ := by
  rw [inv_pow]
  rw [← Complex.ofReal_pow]
  rw [Real.sq_sqrt hx]

end H084Guide

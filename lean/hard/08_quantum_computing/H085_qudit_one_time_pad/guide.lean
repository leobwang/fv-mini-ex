/- Guide for H085 (Qudit one-time pad, the Weyl twirl).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the fixed moduli `ZMod 4` and
`ZMod 5`, a generic primitive root `ζ`, `cexp (t * I)` for real `t`, a generic `f`/`g` sum).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix Complex

namespace H085Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Conjugating by a matrix with one nonzero entry per row -/

/-! ### R1. `constructor` on `A ↔ B` · goal list: `A ↔ B` → `A → B`, `B → A` -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exact hab
  exact hba

/-! ### R2. `subst h` · context: `h : x = e` (x a local variable) is used up, `x` becomes `e` everywhere
Also works with `h : e = x`. After `intro h`, `subst h` turns `x = j + a → j = x - a` into
`j = j + a - a`. -/
example {G : Type} [AddCommGroup G] (x j a : G) (P : G → G → Prop) (k : ∀ y, P (y + a) y)
    (h : x = j + a) : P x j := by
  subst h
  exact k j

/-! ### R3. `ring` in `ZMod d` · closes an identity of a commutative ring; `ZMod d` is one -/
example {d : ℕ} (j a : ZMod d) : j = j + a - a := by
  ring

/-! ### R4. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) (i k : n) (P : ℂ → Prop)
    (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R5. `Matrix.conjTranspose_apply` · goal: `Mᴴ i j` → `star (M j i)` -/
example {n : Type} (M : Matrix n n ℂ) (i j : n) (P : ℂ → Prop) (h : P (star (M j i))) :
    P (Mᴴ i j) := by
  rw [Matrix.conjTranspose_apply]
  exact h

/-! ### R6. `Matrix.of_apply` · goal: `Matrix.of f i j` → `f i j`
`Matrix.of f` is the matrix whose entries are given by the function `f : n → n → α`. To reach it,
first unfold the name of your matrix (`simp only [name]`, as in `simp only [name, Matrix.of_apply]`). -/
example {n : Type} (f : n → n → ℂ) (i j : n) (P : ℂ → Prop) (h : P (f i j)) :
    P (Matrix.of f i j) := by
  rw [Matrix.of_apply]
  exact h

/-! ### R7. `simp only [h]` with `h : ∀ x, p x ↔ q x` · goal: a condition inside `if` replaced
`rw` would fail here when the condition mentions a bound variable; `simp only` rewrites under
binders and fixes up the `Decidable` instance of the `if`. -/
example {α : Type} (p q : α → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ x, p x ↔ q x)
    (u v : ℂ) (x : α) (P : ℂ → Prop) (k : P (if q x then u else v)) : P (if p x then u else v) := by
  simp only [h]
  exact k

/-! ### R8. `ite_mul`, `zero_mul` · goal: `(if c then a else 0) * b` → `if c then a * b else 0` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (h : P (if c then a * b else 0)) :
    P ((if c then a else 0) * b) := by
  simp only [ite_mul, zero_mul]
  exact h

/-! ### R9. `mul_ite`, `mul_zero` · goal: `b * (if c then a else 0)` → `if c then b * a else 0` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (h : P (if c then b * a else 0)) :
    P (b * if c then a else 0) := by
  simp only [mul_ite, mul_zero]
  exact h

/-! ### R10. `apply_ite (star : ℂ → ℂ)`, `star_zero` · goal: `star (if c then a else 0)` → `if c then star a else 0`
`apply_ite f : f (if c then x else y) = if c then f x else f y`; name the function `f` explicitly. -/
example (c : Prop) [Decidable c] (a : ℂ) (P : ℂ → Prop) (h : P (if c then star a else 0)) :
    P (star (if c then a else 0)) := by
  simp only [apply_ite (star : ℂ → ℂ), star_zero]
  exact h

/-! ### R11. `Finset.sum_ite_eq'` · goal: `∑ x ∈ s, if x = a then f x else 0` → `if a ∈ s then f a else 0`
The unprimed `Finset.sum_ite_eq` is the same with `a = x`. A sum over all of a finite type prints
as `∑ x, …`; it is the sum over `Finset.univ`. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι) (f : ι → ℂ) (P : ℂ → Prop)
    (h : P (if a ∈ Finset.univ then f a else 0)) : P (∑ x, if x = a then f x else 0) := by
  rw [Finset.sum_ite_eq']
  exact h

/-! ### R12. `Finset.mem_univ`, `if_true` · goal: `if a ∈ Finset.univ then u else v` → `u` -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι) (u v : ℂ) (P : ℂ → Prop) (h : P u) :
    P (if a ∈ Finset.univ then u else v) := by
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ### R13. `RCLike.star_def` · goal: `star z` → `(starRingEnd ℂ) z` (the same conjugate, other name)
`star` is the general involution; on `ℂ` it is complex conjugation, which Mathlib states its lemmas
for under the name `starRingEnd ℂ`. -/
example (z : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z)) : P (star z) := by
  simp only [RCLike.star_def]
  exact h

/-! ## Part 2 · From `ZMod d` to `Finset.range d` -/

/-! ### R14. `obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)` · context: `d` → `n + 1`
`[NeZero d]` is the instance "`d ≠ 0`"; `NeZero.ne d : d ≠ 0` extracts it. `rfl` in the pattern
substitutes the equation at once. -/
example (d : ℕ) [NeZero d] (P : ℕ → Prop) (k : ∀ n, P (n + 1)) : P d := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  exact k n

/-! ### R15. `Fin.sum_univ_eq_sum_range` · goal: `∑ i : Fin n, f ↑i` → `∑ i ∈ Finset.range n, f i`
`↑i` is `i.val : ℕ`. `Finset.range n = {0, …, n-1}`. -/
example (f : ℕ → ℂ) (n : ℕ) (P : ℂ → Prop) (h : P (∑ i ∈ Finset.range n, f i)) :
    P (∑ i : Fin n, f ↑i) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact h

/-! ## Part 3 · Roots of unity and the geometric sum -/

/-! ### R16. `Complex.isPrimitiveRoot_exp` · context gains `IsPrimitiveRoot (cexp (2 * ↑π * I / ↑n)) n`
`IsPrimitiveRoot ζ k`: `ζ ^ k = 1`, and `ζ ^ l = 1` only when `k ∣ l`. `cexp` is `Complex.exp`. -/
example (n : ℕ) (hn : n ≠ 0) (G : Prop)
    (k : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n → G) : G := by
  have hp := Complex.isPrimitiveRoot_exp n hn
  exact k hp

/-! ### R17. `IsPrimitiveRoot.ne_zero` · `hp.ne_zero (hk : k ≠ 0) : ζ ≠ 0` -/
example (ζ : ℂ) (k : ℕ) (hp : IsPrimitiveRoot ζ k) (hk : k ≠ 0) : ζ ≠ 0 := by
  exact hp.ne_zero hk

/-! ### R18. `unfold D` · goal: the defined name `D` → its body -/
noncomputable def D (t : ℝ) : ℂ := Complex.exp (t * Complex.I)
example (t : ℝ) (P : ℂ → Prop) (h : P (Complex.exp (t * Complex.I))) : P (D t) := by
  unfold D
  exact h

/-! ### R19. `rw [← Complex.exp_conj]` · goal: `conj (cexp x)` → `cexp (conj x)`
`Complex.exp_conj : cexp (conj x) = conj (cexp x)`; `conj` prints as `(starRingEnd ℂ)`. -/
example (x : ℂ) (P : ℂ → Prop) (h : P (Complex.exp ((starRingEnd ℂ) x))) :
    P ((starRingEnd ℂ) (Complex.exp x)) := by
  rw [← Complex.exp_conj]
  exact h

/-! ### R20. `rw [← Complex.exp_neg]` · goal: `(cexp x)⁻¹` → `cexp (-x)` -/
example (x : ℂ) (P : ℂ → Prop) (h : P (Complex.exp (-x))) : P (Complex.exp x)⁻¹ := by
  rw [← Complex.exp_neg]
  exact h

/-! ### R21. `congr 1` · goal: `f a = f b` → `a = b` (strip one function application on both sides)
`congr 1` closes the new goal by itself when it is `rfl` or a hypothesis. -/
example (a b : ℂ) (k : ∀ x y : ℂ, x = y) : Complex.exp a = Complex.exp b := by
  congr 1
  exact k a b

/-! ### R22. `simp [map_ofNat]` · goal: conjugate of an expression in numerals, real casts and `I`
`simp` pushes `conj` through `*`, `/` (`map_mul`, `map_div₀`), fixes real casts (`Complex.conj_ofReal`)
and casts of naturals (`map_natCast`), sends `I` to `-I` (`Complex.conj_I`); `map_ofNat` fixes the
numeral `2`. What is left is a sign to move, for `ring`. -/
example (r : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P (-(2 * ↑r * I) / ↑n)) :
    P ((starRingEnd ℂ) (2 * ↑r * I / ↑n)) := by
  simp [map_ofNat]
  exact h

/-! ### R23. `set r := e with hr` · goal: every `e` → `r`; context gains `r : ℂ := e` and `hr : r = e` -/
example (a b : ℂ) (P : ℂ → Prop) (k : ∀ y, P y) : P (a * b⁻¹) := by
  set r := a * b⁻¹ with hr
  exact k r

/-! ### R24. `map_pow` · goal: `conj (a ^ n)` → `conj a ^ n` -/
example (a : ℂ) (n : ℕ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a ^ n)) :
    P ((starRingEnd ℂ) (a ^ n)) := by
  rw [map_pow]
  exact h

/-! ### R25. `mul_pow` · goal: `(a * b) ^ n` → `a ^ n * b ^ n` -/
example {α : Type} [CommMonoid α] (a b : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n * b ^ n)) :
    P ((a * b) ^ n) := by
  rw [mul_pow]
  exact h

/-! ### R26. `inv_pow` · goal: `a⁻¹ ^ n` → `(a ^ n)⁻¹` -/
example {α : Type} [DivisionMonoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n)⁻¹) :
    P (a⁻¹ ^ n) := by
  rw [inv_pow]
  exact h

/-! ### R27. `pow_mul` · `a ^ (m * n) = (a ^ m) ^ n`; `rw [← pow_mul]` goes back -/
example {α : Type} [Monoid α] (a : α) (m n : ℕ) (P : α → Prop) (h : P (a ^ (m * n))) :
    P ((a ^ m) ^ n) := by
  rw [← pow_mul]
  exact h

/-! ### R28. `rw [mul_comm m]` · goal: the first product `m * _` → `_ * m`
Giving the left factor picks which product turns around. -/
example (m n k : ℕ) (P : ℕ → Prop) (h : P (n * m + k * n)) : P (m * n + k * n) := by
  rw [mul_comm m]
  exact h

/-! ### R29. `simp_rw [h]` · goal: rewrite with `h : ∀ i, f i = g i` under a binder such as `∑ i, …`
`rw [h]` fails here: the `i` inside the sum is bound, so `rw` cannot instantiate `h`. -/
example {ι : Type} [Fintype ι] (f g : ι → ℂ) (h : ∀ i, f i = g i) (P : ℂ → Prop)
    (k : P (∑ i, g i)) : P (∑ i, f i) := by
  simp_rw [h]
  exact k

/-! ### R30. `split_ifs with h` · goal list: a goal with `if c then a else b` → `h : c ⊢ … a …`, `h : ¬c ⊢ … b …` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (ha : c → P a) (hb : ¬c → P b) :
    P (if c then a else b) := by
  split_ifs with h
  exact ha h
  exact hb h

/-! ### R31. `mul_inv_cancel₀` · `a ≠ 0 → a * a⁻¹ = 1` · goal: `a * a⁻¹` → `1` -/
example (a : ℂ) (ha : a ≠ 0) (P : ℂ → Prop) (h : P 1) : P (a * a⁻¹) := by
  rw [mul_inv_cancel₀ ha]
  exact h

/-! ### R32. `simp` on `∑ k ∈ Finset.range n, 1 ^ k` · goal: the sum → `↑n`
(`one_pow`, `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`, `mul_one`) -/
example (n : ℕ) (P : ℂ → Prop) (h : P ↑n) : P (∑ k ∈ Finset.range n, (1 : ℂ) ^ k) := by
  simp
  exact h

/-! ### R33. `intro h` on `a ≠ b` · goal `a ≠ b` → context gains `h : a = b`, goal `False`
`a ≠ b` is by definition `a = b → False`. -/
example (a b : ℂ) (k : a = b → False) : a ≠ b := by
  intro h
  exact k h

/-! ### R34. `rw [mul_inv_eq_one₀ hb] at h` · context: `h : a * b⁻¹ = 1` → `h : a = b`
`mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b`; `rw` with an `↔` rewrites the proposition. -/
example (a b : ℂ) (hb : b ≠ 0) (h : a * b⁻¹ = 1) (G : Prop) (k : a = b → G) : G := by
  rw [mul_inv_eq_one₀ hb] at h
  exact k h

/-! ### R35. `pow_ne_zero` · `pow_ne_zero n (ha : a ≠ 0) : a ^ n ≠ 0` -/
example (a : ℂ) (n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by
  exact pow_ne_zero n ha

/-! ### R36. `IsPrimitiveRoot.pow_inj` · `hp.pow_inj (hi : i < k) (hj : j < k) : ζ ^ i = ζ ^ j → i = j` -/
example (ζ : ℂ) (k i j : ℕ) (hp : IsPrimitiveRoot ζ k) (hi : i < k) (hj : j < k)
    (h : ζ ^ i = ζ ^ j) : i = j := by
  exact hp.pow_inj hi hj h

/-! ### R37. `ZMod.val_lt` · `(x : ZMod n) [NeZero n] : x.val < n`
`x.val : ℕ` is the representative of `x` in `{0, …, n-1}`. -/
example (n : ℕ) [NeZero n] (x : ZMod n) : x.val < n := by
  exact ZMod.val_lt x

/-! ### R38. `ZMod.val_injective` · `ZMod.val_injective n (h : x.val = y.val) : x = y`
`Function.Injective f` unfolds to `∀ a b, f a = f b → a = b`, with `a b` implicit. -/
example (n : ℕ) [NeZero n] (x y : ZMod n) (h : x.val = y.val) : x = y := by
  exact ZMod.val_injective n h

/-! ### R39. `IsPrimitiveRoot.pow_eq_one` · goal: `ζ ^ k` → `1` (`rw [hp.pow_eq_one]`) -/
example (ζ : ℂ) (k : ℕ) (hp : IsPrimitiveRoot ζ k) (P : ℂ → Prop) (h : P 1) : P (ζ ^ k) := by
  rw [hp.pow_eq_one]
  exact h

/-! ### R40. `geom_sum_eq` · `x ≠ 1 → ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1)` · goal rewritten -/
example (x : ℂ) (hx : x ≠ 1) (n : ℕ) (P : ℂ → Prop) (h : P ((x ^ n - 1) / (x - 1))) :
    P (∑ i ∈ Finset.range n, x ^ i) := by
  rw [geom_sum_eq hx]
  exact h

/-! ## Part 4 · Reindexing a sum -/

/-! ### R41. `Equiv.sum_comp` · goal: `∑ i, g (e i)` → `∑ i, g i` for a bijection `e : ι ≃ κ`
`ι ≃ κ` (an `Equiv`) is a bijection packaged with its inverse; `e i` applies it. -/
example {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (g : κ → ℂ) (P : ℂ → Prop)
    (h : P (∑ i, g i)) : P (∑ i, g (e i)) := by
  rw [Equiv.sum_comp]
  exact h

/-! ### R42. `Equiv.subLeft_apply` · goal: `(Equiv.subLeft a) x` → `a - x`
`Equiv.subLeft a : G ≃ G` is the bijection `x ↦ a - x` (it is its own inverse). -/
example {G : Type} [AddGroup G] (a x : G) (P : G → Prop) (h : P (a - x)) :
    P ((Equiv.subLeft a) x) := by
  rw [Equiv.subLeft_apply]
  exact h

/-! ### R43. `Matrix.trace`, `Matrix.diag` · goal: `M.trace` → `∑ i, M i i` -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (P : ℂ → Prop) (h : P (∑ i, M i i)) :
    P M.trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact h

/-! ## Part 5 · Entries of the averaged matrix -/

/-! ### R44. `Nat.cast_ne_zero` · `(↑n : R) ≠ 0 ↔ n ≠ 0` (in `ℂ`, `ℝ`, …); `.mpr` goes right to left -/
example (n : ℕ) (hn : n ≠ 0) : (n : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr hn

/-! ### R45. `Matrix.smul_apply`, `smul_eq_mul` · goal: `(c • M) i j` → `c * M i j` -/
example {n : Type} (c : ℂ) (M : Matrix n n ℂ) (i j : n) (P : ℂ → Prop) (h : P (c * M i j)) :
    P ((c • M) i j) := by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact h

/-! ### R46. `Matrix.sum_apply` · goal: entry of a sum of matrices → sum of the entries -/
example {n ι : Type} [Fintype ι] (g : ι → Matrix n n ℂ) (i j : n) (P : ℂ → Prop)
    (h : P (∑ c, g c i j)) : P ((∑ c, g c) i j) := by
  rw [Matrix.sum_apply]
  exact h

/-! ### R47. `Finset.sum_mul` · `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; `←` pulls a common right factor out -/
example {ι : Type} [Fintype ι] (f : ι → ℂ) (a : ℂ) (P : ℂ → Prop) (h : P ((∑ i, f i) * a)) :
    P (∑ i, f i * a) := by
  rw [← Finset.sum_mul]
  exact h

/-! ### R48. `Matrix.one_apply` · goal: `(1 : Matrix n n α) i j` → `if i = j then 1 else 0` -/
example {n : Type} [DecidableEq n] (i j : n) (P : ℂ → Prop) (h : P (if i = j then 1 else 0)) :
    P ((1 : Matrix n n ℂ) i j) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R49. `by_cases h : c` · goal list: one goal → `h : c ⊢ G` and `h : ¬c ⊢ G` -/
example (c G : Prop) (hp : c → G) (hn : ¬c → G) : G := by
  by_cases h : c
  exact hp h
  exact hn h

/-! ### R50. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `←` pulls a common left factor out -/
example {ι : Type} [Fintype ι] (f : ι → ℂ) (a : ℂ) (P : ℂ → Prop) (h : P (a * ∑ i, f i)) :
    P (∑ i, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R51. `field_simp` · closes (or clears the denominators of) an equation in a field, using
hypotheses `hx : x ≠ 0` from the context for each denominator `x` -/
example (x y : ℂ) (hx : x ≠ 0) : 1 / x ^ 3 * (x * y) = y / x ^ 2 * 1 := by
  field_simp

/-! ### R52. `simpa using h` · simplify `h` and the goal the same way, then close the goal with `h`
`simp` knows `sub_left_inj : a - b = c - b ↔ a = c`. -/
example {G : Type} [AddCommGroup G] (x y a : G) (h : x - a = y - a) : x = y := by
  simpa using h

/-! ### R53. `if_neg` · goal: `if c then a else b` → `b` given `hc : ¬c`
`simp [hc]` does the same, also under a `∑`, and then cleans `0 * x`, `∑ x, 0`, … -/
example (c : Prop) [Decidable c] (hc : ¬c) (a b : ℂ) (P : ℂ → Prop) (h : P b) :
    P (if c then a else b) := by
  rw [if_neg hc]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A concrete modulus: `ZMod 4` IS `Fin 4`, so `exact` works without R14
For a variable `d`, `ZMod d` is stuck (it could be `ZMod 0 = ℤ`); R14 makes `d` a successor first. -/
example (f : ℕ → ℂ) : ∑ b : ZMod 4, f b.val = ∑ k ∈ Finset.range 4, f k := by
  exact Fin.sum_univ_eq_sum_range f 4

/-! ### W2. A geometric sum of a root of unity `ζ ≠ 1` vanishes: R40, R39, then `simp` -/
example (ζ : ℂ) (k : ℕ) (hp : IsPrimitiveRoot ζ k) (h1 : ζ ≠ 1) :
    ∑ i ∈ Finset.range k, ζ ^ i = 0 := by
  rw [geom_sum_eq h1]
  rw [hp.pow_eq_one]
  simp

/-! ### W3. Conjugation of `cexp (t * I)` by R19, R20, R21, R22 -/
example (t : ℝ) : (starRingEnd ℂ) (Complex.exp (t * I)) = (Complex.exp (t * I))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp

/-! ### W4. Collapse a sum with one nonzero term: R8, R11, R12 -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι) (f g : ι → ℂ) :
    ∑ x, (if x = a then f x else 0) * g x = f a * g a := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

/-! ### W5. Reindex by `x ↦ a - x`: R41 with the function written out (an `exact`, not a `rw`) -/
example (a : ZMod 5) (g : ZMod 5 → ℂ) : ∑ x, g (a - x) = ∑ x, g x := by
  exact Equiv.sum_comp (Equiv.subLeft a) g

end H085Guide

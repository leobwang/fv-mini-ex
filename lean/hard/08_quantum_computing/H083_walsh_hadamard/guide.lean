/- Guide for H083 (Walsh–Hadamard: Bernstein–Vazirani and Deutsch–Jozsa).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other products of sums, other
`Fin 2` identities, other double sums).
Infoview: `∑ x, f x` is `Finset.sum Finset.univ f`; `↑a` for `a : Fin 2` is `a.val : ℕ`; `↑√r` is the real
`Real.sqrt r` cast to `ℂ`; `{x | p x}` is the Finset `Finset.univ.filter p`; `∑ x with p x, f x` sums over it.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H083Guide

/-! # Part R · Reference entries -/

/-! ## Sums and products of powers (Part 1, MILESTONE `char_sum`) -/

/-! ### R1. `simp_rw [h]` · goal: rewrites under a binder (`∑ i, …`, `fun i => …`), where `rw` cannot
`h : ∀ i, f i = g i` rewrites `f i` for the bound `i`. `simp_rw [D]` unfolds a definition the same way. -/
example {ι β : Type} [Fintype ι] [AddCommMonoid β] (f g : ι → β) (hfg : ∀ i, f i = g i)
    (P : β → Prop) (h : P (∑ i, g i)) : P (∑ i, f i) := by
  simp_rw [hfg]
  exact h

/-! ### R2. `Finset.prod_pow_eq_pow_sum` · `∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i`; `←` splits a power of a sum -/
example {ι M : Type} [Fintype ι] [CommMonoid M] (f : ι → ℕ) (a : M) (P : M → Prop)
    (h : P (∏ i, a ^ f i)) : P (a ^ ∑ i, f i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact h

/-! ### R3. `Fintype.prod_sum` · `∏ i, ∑ j, f i j = ∑ x, ∏ i, f i (x i)`; `rw [← Fintype.prod_sum f]` · goal
Right to left it turns a sum over all functions `x : ι → κ` into a product of small sums. Give `f`
explicitly: `rw` cannot guess a two-argument function from the pattern `f i (x i)`. -/
example {ι κ R : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommSemiring R] (f : ι → κ → R)
    (P : R → Prop) (h : P (∏ i, ∑ j, f i j)) : P (∑ x : ι → κ, ∏ i, f i (x i)) := by
  rw [← Fintype.prod_sum f]
  exact h

/-! ### R4. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R5. `Fin.val_zero`, `Fin.val_one` · goal: `↑(0 : Fin 2)` → `0`, `↑(1 : Fin 2)` → `1` (as `ℕ`) -/
example (P : ℕ → ℕ → Prop) (h : P 0 1) : P (0 : Fin 2).val (1 : Fin 2).val := by
  simp only [Fin.val_zero, Fin.val_one]
  exact h

/-! ### R6. `mul_zero`, `mul_one`, `one_mul`, `pow_zero` · goal: arithmetic clean-up
`a * 0 = 0`, `a * 1 = a`, `1 * a = a`, `a ^ 0 = 1`. -/
example {M : Type} [CommSemiring M] (c : M) (a : ℕ) (P : M → Prop) (h : P (1 + c ^ a)) :
    P (c ^ (a * 0) + 1 * c ^ (a * 1)) := by
  simp only [mul_zero, mul_one, one_mul, pow_zero]
  exact h

/-! ### R7. `split_ifs with h` · goal list: `P (if c then a else b)` → one goal per branch, with `h` -/
example {α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop) (ha : P a) (hb : P b) :
    P (if c then a else b) := by
  split_ifs with h
  exacts [ha, hb]

/-! ### R8. `subst h` · context: `h : x = e` with `x` a local variable; every `x` becomes `e`, `h` is gone
If both sides are variables, the right-hand one is eliminated. -/
example (P : ℕ → Prop) (x : ℕ) (hx : x = 0) (h : P 0) : P x := by
  subst hx
  exact h

/-! ### R9. `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin` · goal: `∏ _i : Fin n, c` → `c ^ n`
`norm_num` and `simp` apply these by themselves (with `Pi.zero_apply`, R5, R6). -/
example {M : Type} [CommMonoid M] (n : ℕ) (c : M) (P : M → Prop) (h : P (c ^ n)) :
    P (∏ _i : Fin n, c) := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact h

/-! ### R10. `obtain ⟨i, hi⟩ : ∃ i, Q i := proof` · context gains a witness `i` and `hi : Q i` -/
example {ι : Type} (Q : ι → Prop) (hex : ∃ i, Q i) (G : Prop) (g : ∀ i, Q i → G) : G := by
  obtain ⟨i, hi⟩ : ∃ i, Q i := hex
  exact g i hi

/-! ### R11. `by_contra hc` · goal `G` → `False`; context gains `hc : ¬G` -/
example (G : Prop) (hng : ¬¬G) : G := by
  by_contra hc
  exact hng hc

/-! ### R12. `push Not at hc` · context: pushes `¬` inward: `¬∃ i, a i ≠ b` → `∀ i, a i = b`
`push_neg at hc` is the older name of the same step. -/
example {ι β : Type} (a : ι → β) (b : β) (hc : ¬∃ i, a i ≠ b) : ∀ i, a i = b := by
  push Not at hc
  exact hc

/-! ### R13. `funext hc` (term) · `(∀ i, f i = g i) → f = g`: build a function equality from pointwise ones -/
example {ι β : Type} (f g : ι → β) (hc : ∀ i, f i = g i) (hne : ¬f = g) : False := by
  exact hne (funext hc)

/-! ### R14. `Finset.prod_eq_zero` with `Finset.mem_univ` · goal: `∏ j, f j = 0` → `f i = 0`
`Finset.prod_eq_zero : i ∈ s → f i = 0 → ∏ j ∈ s, f j = 0`; `Finset.mem_univ i : i ∈ Finset.univ`. -/
example {ι M₀ : Type} [Fintype ι] [CommMonoidWithZero M₀] (f : ι → M₀) (i : ι) (hi : f i = 0) :
    ∏ j, f j = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact hi

/-! ### R15. `omega` on `Fin 2` · context gains `a = 1` from `a ≠ 0` (it knows `a.val < 2`) -/
example (a : Fin 2) (ha : a ≠ 0) (G : Prop) (g : a = 1 → G) : G := by
  have h1 : a = 1 := by omega
  exact g h1

/-! ## Characters multiply (Part 2, MILESTONE `neg_one_pow_dot_add`) -/

/-! ### R16. `Finset.prod_mul_distrib` · `∏ i, f i * g i = (∏ i, f i) * ∏ i, g i`; `←` merges two products -/
example {ι M : Type} [Fintype ι] [CommMonoid M] (f g : ι → M) (P : M → Prop)
    (h : P (∏ i, f i * g i)) : P ((∏ i, f i) * ∏ i, g i) := by
  rw [← Finset.prod_mul_distrib]
  exact h

/-! ### R17. `Pi.add_apply`, `Pi.zero_apply` · goal: `(f + g) i` → `f i + g i`, `(0 : ι → β) i` → `0`
On bit strings `x + y` is pointwise; on `Fin 2`, `+` is XOR (`1 + 1 = 0`). -/
example {ι β : Type} [AddZeroClass β] (f g : ι → β) (i : ι) (P : β → β → Prop)
    (h : P (f i + g i) 0) : P ((f + g) i) ((0 : ι → β) i) := by
  simp only [Pi.add_apply, Pi.zero_apply]
  exact h

/-! ### R18. `refine Finset.prod_congr rfl fun i _ => ?_` · goal: equal products → equal factors
`Finset.prod_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g`. -/
example {ι M : Type} [Fintype ι] [CommMonoid M] (f g : ι → M) (hfg : ∀ i, f i = g i) :
    ∏ i, f i = ∏ i, g i := by
  refine Finset.prod_congr rfl fun i _ => ?_
  exact hfg i

/-! ### R19. `generalize e = a` · goal: the term `e` → a fresh variable `a`; context gains `a`
`fin_cases` needs a variable, not `x i`. Only the goal is changed: `revert` hypotheses first (R24). -/
example {ι α : Type} (x : ι → α) (i : ι) (P : α → Prop) (h : ∀ a, P a) : P (x i) := by
  generalize x i = a
  exact h a

/-! ### R20. `show (1 + 1 : Fin 2) = 0 from rfl` · a fact proved on the spot, to pass to `rw`/`simp`
`Fin 2` arithmetic is mod 2, so the fact holds by computation (`rfl`, or `decide`). -/
example (P : Fin 2 → Prop) (h : P 0) : P (1 + 1) := by
  rw [show (1 + 1 : Fin 2) = 0 from rfl]
  exact h

/-! ## Symmetry and bit strings (Parts 3–4, MILESTONES `dot_comm`, `bits_add_eq_zero`) -/

/-! ### R21. `simp [mul_comm]` · closes sums equal up to commuting each product
`simp` uses `mul_comm` only when it puts the factors in a fixed order, so it does not loop. -/
example {ι R : Type} [Fintype ι] [CommSemiring R] (f g : ι → R) :
    ∑ i, f i * g i = ∑ i, g i * f i := by
  simp [mul_comm]

/-! ### R22. `have := congrFun h i` · context gains `this : f i = g i` from `h : f = g` -/
example {ι β : Type} (f g : ι → β) (h : f = g) (i : ι) (G : Prop) (k : f i = g i → G) : G := by
  have := congrFun h i
  exact k this

/-! ### R23. `simp only [l] at h` · context: rewrites the hypothesis `h`, goal unchanged -/
example {ι β : Type} [AddZeroClass β] (f g : ι → β) (i : ι) (hi : (f + g) i = (0 : ι → β) i)
    (G : Prop) (k : f i + g i = 0 → G) : G := by
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  exact k hi

/-! ### R24. `revert h` · context loses `h : T`; goal `G` → `T → G` -/
example (T G : Prop) (h : T) (k : T → G) : G := by
  revert h
  exact k

/-! ### R25. `rintro rfl` · goal `a = b → G` → `G` with `b` replaced by `a` -/
example {α : Type} (a b : α) (P : α → α → Prop) (h : ∀ x, P x x) : a = b → P a b := by
  rintro rfl
  exact h a

/-! ## The normalisation `(2^{-n/2})² = 2^{-n}` (Parts 5–6) -/

/-! ### R26. `inv_pow` · `a⁻¹ ^ n = (a ^ n)⁻¹` · goal -/
example {α : Type} [DivisionMonoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n)⁻¹) :
    P (a⁻¹ ^ n) := by
  rw [inv_pow]
  exact h

/-! ### R27. `Complex.ofReal_pow` · `↑(r ^ n) = ↑r ^ n`; `←` moves `^` inside the cast `ℝ → ℂ` -/
example (r : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P ↑(r ^ n)) : P (↑r ^ n) := by
  rw [← Complex.ofReal_pow]
  exact h

/-! ### R28. `Real.sq_sqrt` · `0 ≤ r → √r ^ 2 = r`; `rw [Real.sq_sqrt (by positivity)]` · goal -/
example (r : ℝ) (hr : 0 ≤ r) (P : ℝ → Prop) (h : P r) : P (√r ^ 2) := by
  rw [Real.sq_sqrt hr]
  exact h

/-! ### R29. `positivity` · closes `0 ≤ e` or `0 < e` for `e` built from positive pieces (`2 ^ n`, `√`, `exp`) -/
example (n : ℕ) : (0 : ℝ) ≤ 3 ^ n := by positivity

/-! ### R30. `push_cast` · goal: casts moved inward, `↑((3 : ℝ) ^ n)` → `(3 : ℂ) ^ n`
It may leave `t = t` whose two sides print alike but differ invisibly; close that with `rfl`. -/
example (n : ℕ) (P : ℂ → Prop) (h : P ((3 : ℂ) ^ n)) : P (((3 : ℝ) ^ n : ℝ) : ℂ) := by
  push_cast
  exact h

/-! ## Moving scalars and swapping sums (Parts 5–7) -/

/-! ### R31. `Finset.mul_sum` · `a * ∑ i, f i = ∑ i, a * f i`; forward pushes `a` in, `←` pulls it out -/
example {ι R : Type} [Fintype ι] [CommSemiring R] (a : R) (f : ι → R) (P : R → Prop)
    (h : P (∑ i, a * f i)) : P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R32. `mul_assoc` · `a * b * c = a * (b * c)`; `←` flattens to the left-nested `a * b * c` -/
example {M : Type} [Semigroup M] (a b c : M) (P : M → Prop) (h : P (a * b * c)) :
    P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R33. `Finset.sum_comm` · `∑ x, ∑ y, f x y = ∑ y, ∑ x, f x y` · goal: swap two sums -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → β → M) (P : M → Prop)
    (h : P (∑ y, ∑ x, f x y)) : P (∑ x, ∑ y, f x y) := by
  rw [Finset.sum_comm]
  exact h

/-! ### R34. `field_simp` · closes (or clears the denominators of) an equation with `⁻¹`, `/`
It needs each denominator `≠ 0`; it proves `3 ^ n ≠ 0` in `ℂ` by itself. -/
example (b : ℂ) (n : ℕ) : (3 ^ n : ℂ)⁻¹ * b * 3 ^ n = b := by
  field_simp

/-! ### R35. `Finset.sum_ite_eq'` · `(∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0` · goal
`Finset.sum_ite_eq` is the twin with `a = x` in the test. -/
example {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (a : ι) (b : ι → M)
    (P : M → Prop) (h : P (if a ∈ Finset.univ then b a else 0)) :
    P (∑ x, if x = a then b x else 0) := by
  rw [Finset.sum_ite_eq']
  exact h

/-! ### R36. `Finset.mem_univ`, `if_true` · goal: `if a ∈ Finset.univ then u else v` → `u` -/
example {ι M : Type} [Fintype ι] [DecidableEq ι] (a : ι) (u v : M) (P : M → Prop) (h : P u) :
    P (if a ∈ Finset.univ then u else v) := by
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ## Basis vectors (Part 6, `bernstein_vazirani`) -/

/-! ### R37. `sq` · `a ^ 2 = a * a`; `←` folds `a * a` into `a ^ 2` · goal -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P (a ^ 2)) : P (a * a) := by
  rw [← sq]
  exact h

/-! ### R38. `Pi.single_apply` · `Pi.single i x i' = if i' = i then x else 0` · goal
`Pi.single s 1` is the function that is `1` at `s` and `0` elsewhere: the basis state `|s⟩`. -/
example {ι M : Type} [DecidableEq ι] [Zero M] (s y : ι) (u : M) (P : M → Prop)
    (h : P (if y = s then u else 0)) : P ((Pi.single s u : ι → M) y) := by
  rw [Pi.single_apply]
  exact h

/-! ### R39. `eq_comm (a := s)` · `s = y ↔ y = s`, only for equations whose left side is `s` · goal
Without `(a := s)`, `simp` would flip every equation and could loop. -/
example {ι M : Type} [DecidableEq ι] (s y : ι) (u v : M) (P : M → Prop)
    (h : P (if y = s then u else v)) : P (if s = y then u else v) := by
  simp only [eq_comm (a := s)]
  exact h

/-! ## Splitting a sum by a predicate (Part 7, `deutsch_jozsa`) -/

/-! ### R40. `Finset.sum_filter_add_sum_filter_not` · `←` splits `∑ x ∈ s, f x` by `p`
`∑ x ∈ s with p x, f x + ∑ x ∈ s with ¬p x, f x = ∑ x ∈ s, f x`. Give `s` and `p` explicitly. -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (p : ι → Prop) [DecidablePred p] (f : ι → M)
    (P : M → Prop) (h : P (∑ x with p x, f x + ∑ x with ¬p x, f x)) : P (∑ x, f x) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]
  exact h

/-! ### R41. `simp at hx` on a filter membership (`Finset.mem_filter`, `Finset.mem_univ`) · context
`hx : x ∈ {x | p x}` (the Finset `Finset.univ.filter p`) becomes `hx : p x`. -/
example {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (x : ι)
    (hx : x ∈ Finset.univ.filter p) : p x := by
  simp at hx
  exact hx

/-! ### R42. `Finset.sum_congr rfl h0` · `rw` with it: rewrite each term of a sum using `h0 : ∀ x ∈ s, f x = g x` -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (p : ι → Prop) [DecidablePred p] (f : ι → M) (c : M)
    (h0 : ∀ x ∈ Finset.univ.filter p, f x = c) (Q : M → Prop) (h : Q (∑ _x with p _x, c)) :
    Q (∑ x with p x, f x) := by
  rw [Finset.sum_congr rfl h0]
  exact h

/-! ### R43. `Finset.sum_const` · `∑ _x ∈ s, c = s.card • c` · goal
`k • c` for `k : ℕ` is `c + ⋯ + c` (`k` copies). -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (p : ι → Prop) [DecidablePred p] (c : M)
    (Q : M → Prop) (h : Q ((Finset.univ.filter p).card • c)) : Q (∑ _x with p _x, c) := by
  rw [Finset.sum_const]
  exact h

/-! ### R44. `ext x` on Finsets (`Finset.ext`) · goal `s = t` → `x ∈ s ↔ x ∈ t` -/
example {ι : Type} [Fintype ι] (p q : ι → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) : Finset.univ.filter p = Finset.univ.filter q := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hpq x

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A sum over bit strings of a product, as a product of two-term sums: R3 → R4 → R5, R6 -/
example (n : ℕ) : ∑ x : Fin n → Fin 2, ∏ i, (2 : ℂ) ^ (x i).val = 3 ^ n := by
  rw [← Fintype.prod_sum (fun i (b : Fin 2) => (2 : ℂ) ^ b.val)]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  norm_num

/-! ### W2. A `Fin 2` identity by cases: R19 (no `generalize` needed here), `fin_cases`, `simp` -/
example (a b : Fin 2) : (-1 : ℂ) ^ a.val * (-1) ^ b.val = (-1) ^ (a + b).val := by
  fin_cases a <;> fin_cases b <;> simp [show (1 + 1 : Fin 2) = 0 from rfl]

/-! ### W3. Push a scalar into a double sum and swap: R31, R33 -/
example {R : Type} [CommSemiring R] (c : R) (f : Fin 3 → Fin 2 → R) :
    c * ∑ i, ∑ j, f i j = ∑ j, ∑ i, c * f i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### W4. Split a sum by a predicate and count: R40 → R42 → R43 -/
example {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (f : ι → ℤ)
    (h1 : ∀ x ∈ Finset.univ.filter p, f x = 2)
    (h2 : ∀ x ∈ Finset.univ.filter (fun x => ¬p x), f x = 0) :
    ∑ x, f x = (Finset.univ.filter p).card • 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  rw [Finset.sum_const, Finset.sum_const_zero, add_zero]

end H083Guide

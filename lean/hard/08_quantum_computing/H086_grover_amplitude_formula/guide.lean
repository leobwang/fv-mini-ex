/- Guide for H086 (Grover's amplitude formula).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other sums, angles, sequences).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H086Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · functions, case splits and finite sums -/

/-! ### R1. `funext i` · goal `f = g` (functions) → context gains `i`, goal `f i = g i` -/
example {α β : Type} (f g : α → β) (h : ∀ i, f i = g i) : f = g := by
  funext i
  exact h i

/-! ### R2. `by_cases h : p` · goal list: one goal → two, with `h : p` and with `h : ¬p` -/
example (p G : Prop) (h1 : p → G) (h2 : ¬p → G) : G := by
  by_cases h : p
  exacts [h1 h, h2 h]

/-! ### R3. `simp [h]` on an `if` (lemmas `if_pos`, `if_neg`) · goal: `if p then x else y` → the branch `h` picks -/
example {α : Type} (p : Prop) [Decidable p] (x y : α) (Q : α → Prop) (h : p) (hx : Q x) :
    Q (if p then x else y) := by
  simp [h]
  exact hx

example {α : Type} (p : Prop) [Decidable p] (x y : α) (Q : α → Prop) (h : ¬p) (hy : Q y) :
    Q (if p then x else y) := by
  simp [h]
  exact hy

/-! ### R4. `Finset.sum_add_distrib` · goal: `∑ (f i + g i)` → `∑ f i + ∑ g i` -/
example {ι M : Type} [AddCommMonoid M] (s : Finset ι) (f g : ι → M) (P : M → Prop)
    (h : P (∑ i ∈ s, f i + ∑ i ∈ s, g i)) : P (∑ i ∈ s, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R5. `Finset.sum_ite_eq'` · goal: a sum of `if i = a then b i else 0` → one term, guarded by `a ∈ s` -/
example {ι M : Type} [AddCommMonoid M] [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M)
    (P : M → Prop) (h : P (if a ∈ s then b a else 0)) :
    P (∑ i ∈ s, if i = a then b i else 0) := by
  rw [Finset.sum_ite_eq']
  exact h

/-! ### R6. `simp only [Finset.mem_univ, if_true]` · goal: `if a ∈ Finset.univ then x else y` → `x` -/
example {ι M : Type} [Fintype ι] [DecidableEq ι] (a : ι) (x y : M) (P : M → Prop) (h : P x) :
    P (if a ∈ (Finset.univ : Finset ι) then x else y) := by
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ### R7. `Finset.sum_const` · goal: a sum of a constant → `card • c` (`•`: repeated addition) -/
example {ι M : Type} [AddCommMonoid M] (s : Finset ι) (c : M) (P : M → Prop) (h : P (s.card • c)) :
    P (∑ _i ∈ s, c) := by
  rw [Finset.sum_const]
  exact h

/-! ### R8. `Finset.card_univ` · goal: `Finset.univ.card` → `Fintype.card α` -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α)) :
    P (Finset.univ : Finset α).card := by
  rw [Finset.card_univ]
  exact h

/-! ### R9. `Fintype.card_fin` · goal: `Fintype.card (Fin n)` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Fintype.card (Fin n)) := by
  rw [Fintype.card_fin]
  exact h

/-! ### R10. `nsmul_eq_mul` · goal: `n • a` (`n : ℕ`) → `↑n * a` (multiplication in the ring) -/
example (n : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (↑n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R11. `Fin.pos` · `(i : Fin n) → 0 < n` · context gains `0 < n` (`Fin n` has an element, so `n ≠ 0`) -/
example (n : ℕ) (i : Fin n) (G : Prop) (g : 0 < n → G) : G := by
  have hn := i.pos
  exact g hn

/-! ### R12. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` from the shape of `e`; atoms by hypothesis -/
example (n : ℕ) (hn : 0 < n) : (n : ℝ) ≠ 0 := by positivity

example (x : ℝ) (hx : 0 < x) : 0 < 1 / Real.sqrt x + x ^ 2 := by positivity

/-! ### R13. `field_simp` · goal: denominators known `≠ 0` (from the context) are multiplied out -/
example (a b c x : ℝ) (hx : x ≠ 0) (h : a + x * b = x * c) : a / x + b = c := by
  field_simp
  exact h

/-! ## Part 2 · casts, square roots and `arcsin` -/

/-! ### R14. `exact_mod_cast h` · closes a goal that is `h` up to casts `ℕ → ℝ` -/
example (n : ℕ) (h : 2 ≤ n) : (2 : ℝ) ≤ n := by
  exact_mod_cast h

/-! ### R15. `Real.one_le_sqrt` · `1 ≤ √x ↔ 1 ≤ x` · goal: by `rw` -/
example (x : ℝ) (h : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  rw [Real.one_le_sqrt]
  exact h

/-! ### R16. `linarith` · closes a linear (in)equality over `ℝ` that follows from the hypotheses -/
example (x y : ℝ) (h1 : 2 ≤ x) (h2 : y < x - 1) : y < 2 * x := by linarith

/-! ### R17. `apply Real.sin_arcsin` · `-1 ≤ x → x ≤ 1 → sin (arcsin x) = x` · goal → two side goals -/
example (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : Real.sin (Real.arcsin x) = x := by
  apply Real.sin_arcsin
  exacts [h1, h2]

/-! ### R18. `div_le_one` · `0 < b → (a / b ≤ 1 ↔ a ≤ b)` · goal, side goal closed by `(by positivity)` -/
example (a b : ℝ) (hb : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  rw [div_le_one hb]
  exact h

/-! ### R19. `Real.cos_arcsin` · `cos (arcsin x) = √(1 - x ^ 2)` · goal (no side condition) -/
example (x : ℝ) (P : ℝ → Prop) (h : P (Real.sqrt (1 - x ^ 2))) : P (Real.cos (Real.arcsin x)) := by
  rw [Real.cos_arcsin]
  exact h

/-! ### R20. `div_pow` · goal: `(a / b) ^ n` → `a ^ n / b ^ n` -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a ^ n / b ^ n)) : P ((a / b) ^ n) := by
  rw [div_pow]
  exact h

/-! ### R21. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · goal; side goal by `(by linarith)` -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (Real.sqrt x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! ### R22. `one_pow` · goal: `1 ^ n` → `1` -/
example (n : ℕ) (P : ℝ → Prop) (h : P 1) : P ((1 : ℝ) ^ n) := by
  rw [one_pow]
  exact h

/-! ### R23. `rw [show a = b by tac]` · goal: rewrite with an equation proved on the spot -/
example (x : ℝ) (hx : x ≠ 0) (P : ℝ → Prop) (h : P ((x - 1) / x)) : P (1 - 1 / x) := by
  rw [show 1 - 1 / x = (x - 1) / x by field_simp]
  exact h

/-! ### R24. `Real.sqrt_div` · `0 ≤ x → ∀ y, √(x / y) = √x / √y` · goal -/
example (x y : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P (Real.sqrt x / Real.sqrt y)) :
    P (Real.sqrt (x / y)) := by
  rw [Real.sqrt_div hx]
  exact h

/-! ## Part 3 · trigonometry and `linear_combination` -/

/-! ### R25. `obtain ⟨hs, hc⟩ := h` · context: `h : A ∧ B` → `hs : A`, `hc : B` -/
example (A B G : Prop) (h : A ∧ B) (g : A → B → G) : G := by
  obtain ⟨hs, hc⟩ := h
  exact g hs hc

/-! ### R26. `Real.sqrt_pos` · `0 < √x ↔ 0 < x` · a term: `Real.sqrt_pos.mpr h` -/
example (x : ℝ) (hx : 0 < x) (G : Prop) (g : 0 < Real.sqrt x → G) : G := by
  have h3 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  exact g h3

/-! ### R27. `Real.sin_add` · goal: `sin (x + y)` → `sin x * cos y + cos x * sin y` -/
example (x y : ℝ) (P : ℝ → Prop)
    (h : P (Real.sin x * Real.cos y + Real.cos x * Real.sin y)) : P (Real.sin (x + y)) := by
  rw [Real.sin_add]
  exact h

/-! ### R28. `Real.cos_add` · goal: `cos (x + y)` → `cos x * cos y - sin x * sin y` -/
example (x y : ℝ) (P : ℝ → Prop)
    (h : P (Real.cos x * Real.cos y - Real.sin x * Real.sin y)) : P (Real.cos (x + y)) := by
  rw [Real.cos_add]
  exact h

/-! ### R29. `Real.sin_two_mul` · goal: `sin (2 * x)` → `2 * sin x * cos x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (2 * Real.sin x * Real.cos x)) : P (Real.sin (2 * x)) := by
  rw [Real.sin_two_mul]
  exact h

/-! ### R30. `Real.cos_two_mul` · goal: `cos (2 * x)` → `2 * cos x ^ 2 - 1` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (2 * Real.cos x ^ 2 - 1)) : P (Real.cos (2 * x)) := by
  rw [Real.cos_two_mul]
  exact h

/-! ### R31. `linear_combination e * h` · closes `L = R` when `L - R - e * (lhs h - rhs h)` is `0` by `ring` -/
example (s x y : ℝ) (h : s ^ 2 = x) : y * s ^ 2 + 1 = y * x + 1 := by
  linear_combination y * h

/-! ## Part 4 · induction on a recursive definition -/

/-- a sequence defined by pattern matching, like `grover m` (not the exercise's) -/
noncomputable def seq (c : ℝ) : ℕ → ℝ
  | 0 => c
  | k + 1 => 2 * seq c k

/-! ### R32. `induction k with | zero => … | succ k ih => …` · goal list: base case and step with `ih` -/
example (Q : ℕ → Prop) (h0 : Q 0) (hs : ∀ k, Q k → Q (k + 1)) (k : ℕ) : Q k := by
  induction k with
    | zero => ?_
    | succ k ih => ?_
  exact h0
  exact hs k ih

/-! ### R33. `simp only [seq]` / `rw [seq]` · goal: `seq c 0` or `seq c (k + 1)` → that clause's right side -/
example (c : ℝ) (P : ℝ → Prop) (h : P c) : P (seq c 0) := by
  simp only [seq]
  exact h

example (c : ℝ) (k : ℕ) (P : ℝ → Prop) (h : P (2 * seq c k)) : P (seq c (k + 1)) := by
  rw [seq]
  exact h

/-! ### R34. `simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]` · goal: `(2 * ↑0 + 1) * x` → `x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) : P ((2 * ((0 : ℕ) : ℝ) + 1) * x) := by
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
  exact h

/-! ### R35. `split_ifs` · goal with `if p then x else y` → one goal per branch, with `h✝ : p` / `h✝ : ¬p` -/
example {α : Type} (p : Prop) [Decidable p] (x y : α) (Q : α → Prop) (hx : Q x) (hy : Q y) :
    Q (if p then x else y) := by
  split_ifs
  exacts [hx, hy]

/-! ### R36. `push_cast` · goal: casts pushed inward: `↑(k + 1)` → `↑k + 1` -/
example (k : ℕ) (P : ℝ → Prop) (h : P ((k : ℝ) + 1)) : P ((k + 1 : ℕ) : ℝ) := by
  push_cast
  exact h

/-! ### R37. `rw [← hf]` with `hf : ∀ φ, f φ = g (φ + c)` · goal: `g (x + c)` → `f x`; Lean finds `φ := x` -/
example (f g : ℝ → ℝ) (c x : ℝ) (hf : ∀ φ, f φ = g (φ + c)) (P : ℝ → Prop) (h : P (f x)) :
    P (g (x + c)) := by
  rw [← hf]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A sum "constant plus one spike" over `Fin n`: R4, R5, R6, R7, R8, R9, R10 -/
example (n : ℕ) (j₀ : Fin n) (b c : ℝ) :
    ∑ j, (b + if j = j₀ then c else 0) = n * b + c := by
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### W2. Rotation by a double angle, given `sin α = s` and `cos α = c`: R27, R29, R30 -/
example (φ α s c : ℝ) (hs : Real.sin α = s) (hc : Real.cos α = c) :
    Real.sin (φ + 2 * α) = Real.sin φ * (2 * c ^ 2 - 1) + Real.cos φ * (2 * s * c) := by
  rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc]

/-! ### W3. A square root in a denominator: R26, R13, R31 against `√x ^ 2 = x` -/
example (x : ℝ) (hx : 0 < x) : x / Real.sqrt x = Real.sqrt x := by
  have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h3 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  field_simp
  linear_combination -h1

/-! ### W4. A closed form by induction: R32, R33 with R34-style clean-up lemmas, then the IH and `ring` -/
example (c : ℝ) (k : ℕ) : seq c k = 2 ^ k * c := by
  induction k with
    | zero => simp only [seq, pow_zero, one_mul]
    | succ k ih =>
      rw [seq, ih]
      ring

end H086Guide

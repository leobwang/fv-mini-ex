/- Guide for M132 (Quantum teleportation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (√3, states on `Fin 2 × ℕ`).
Assumed: Lean basics.
-/
import Mathlib

namespace M132Guide

/-! # Part R · Reference entries -/

/-! ## The number `1/√2`: a milestone `s * s = 1 / 2` -/

/-! ### R1. `rw [D]` (a defined constant) · goal: the name `D` → its body -/
noncomputable def t : ℂ := (Real.sqrt 3 : ℂ)⁻¹
example (P : ℂ → Prop) (h : P (Real.sqrt 3 : ℂ)⁻¹) : P t := by
  rw [t]
  exact h

/-! ### R2. `mul_inv` · `(a * b)⁻¹ = a⁻¹ * b⁻¹`; used right to left: `rw [← mul_inv]` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (P : α → Prop) (h : P (a * b)⁻¹) :
    P (a⁻¹ * b⁻¹) := by
  rw [← mul_inv]
  exact h

/-! ### R3. `Complex.ofReal_mul` · `↑(x * y) = ↑x * ↑y`; right to left moves `*` inside the cast -/
example (x y : ℝ) (P : ℂ → Prop) (h : P ↑(x * y)) : P (↑x * ↑y) := by
  rw [← Complex.ofReal_mul]
  exact h

/-! ### R4. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x` · goal rewritten, plus side goal `0 ≤ x`
Write `rw [Real.mul_self_sqrt (by norm_num)]` to close the side goal on the spot. -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x * √x) := by
  rw [Real.mul_self_sqrt]
  exact h
  exact hx

/-! ### R5. `norm_num` · closes a goal made of numerals (`⁻¹`, `/`, casts of numerals included) -/
example : ((3 : ℝ) : ℂ)⁻¹ = 1 / 3 := by norm_num

/-! ## A function equation → finitely many number equations -/

/-! ### R6. `funext ⟨a, b⟩` · goal `f = g` (functions on pairs) → context gains `a b`, goal at `(a, b)`
A right side `fun q => …` is applied to `(a, b)` and reduced. -/
example {α β : Type} (f g : α × β → ℂ) (k : ℂ) (h : ∀ a b, f (a, b) = k * g (a, b)) :
    f = fun q => k * g q := by
  funext ⟨a, b⟩
  exact h a b

/-! ### R7. `have h := lemma` · context gains `h` with the lemma's statement; goal unchanged -/
example (G : Prop) (g : 0 ≤ √3 → G) : G := by
  have h := Real.sqrt_nonneg 3
  exact g h

/-! ### R8. `fin_cases a <;> fin_cases b` · context loses `a b : Fin 2`; goal → one goal per pair
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the value `0`. -/
example (P : Fin 2 → Fin 2 → Prop) (h00 : P 0 0) (h01 : P 0 1) (h10 : P 1 0) (h11 : P 1 1)
    (a b : Fin 2) : P a b := by
  fin_cases a <;> fin_cases b
  exacts [h00, h01, h10, h11]

/-! ## Evaluating one amplitude (`simp [defs]` does R9–R12 in one call) -/

/-! ### R9. `simp only [D]` (a defined function) · goal: `D w q` → the body, applied to `q` -/
def dbl (w : Fin 2 × ℕ → ℂ) : Fin 2 × ℕ → ℂ := fun q => 2 * w q
example (w : Fin 2 × ℕ → ℂ) (c : Fin 2) (n : ℕ) (P : ℂ → Prop) (h : P (2 * w (c, n))) :
    P (dbl w (c, n)) := by
  simp only [dbl]
  exact h

/-! ### R10. Projections of a tuple: `simp` · goal: `(a, b, c).2.1` → `b` -/
example {α β γ : Type} (a : α) (b : β) (c : γ) (P : β → Prop) (h : P b) : P ((a, b, c).2.1) := by
  simp only []
  exact h

/-! ### R11. Arithmetic in `Fin 2`: `simp` · goal: `1 + 1` → `0` (`+` on `Fin 2` is XOR) -/
example (P : Fin 2 → Prop) (h : P 0) : P ((1 : Fin 2) + 1) := by
  simp
  exact h

/-! ### R12. `if` with a condition on numerals: `simp` · goal: `if c then a else b` → `a` or `b` -/
example {α : Type} (a b : α) (P : α → Prop) (h : P b) :
    P (if (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 1 then a else b) := by
  simp
  exact h

/-! ## Closing the number equations -/

/-! ### R13. `ring_nf` · goal in ring normal form: `a * (x * a)` → `a ^ 2 * x` -/
example (a x : ℂ) (P : ℂ → Prop) (h : P (a ^ 2 * x)) : P (a * (x * a)) := by
  ring_nf
  exact h

/-! ### R14. `sq` · `a ^ 2 = a * a` · goal: back from a power to a product, so `h : a * a = …` applies
`simp [sq, h]` does this rewrite and then rewrites with `h`. -/
example {α : Type} [Monoid α] (a : α) (P : α → Prop) (h : P (a * a)) : P (a ^ 2) := by
  rw [sq]
  exact h

/-! ### R15. `ring` · closes an identity of commutative rings; treats `w (0, n)` and `a⁻¹` as unknowns -/
example (x : ℂ) : 2⁻¹ * x = x * 2⁻¹ := by ring

/-! ## Sums of `normSq` -/

/-! ### R16. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) (P : ℝ → Prop)
    (h : P (∑ a, ∑ b, f (a, b))) : P (∑ q, f q) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R17. `simp only [hk]` with `hk : ∀ i, f i = g i` · goal: rewrites inside `∑ i, …`
`rw [hk]` fails here: it cannot rewrite a term that mentions the bound variable `i`. -/
example {α : Type} [Fintype α] (f g : α → ℝ) (hk : ∀ i, f i = g i) (P : ℝ → Prop)
    (h : P (∑ i, g i)) : P (∑ i, f i) := by
  simp only [hk]
  exact h

/-! ### R18. `Complex.normSq_mul` · `normSq (z * w) = normSq z * normSq w` · goal -/
example (z w : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z * Complex.normSq w)) :
    P (Complex.normSq (z * w)) := by
  rw [Complex.normSq_mul]
  exact h

/-! ### R19. `intro Q _` on `∀ Q : Prop, [Decidable Q] → …` · context gains `Q` and an instance -/
example (G : Prop → Prop) (hG : ∀ Q : Prop, [Decidable Q] → G Q) :
    ∀ Q : Prop, [Decidable Q] → G Q := by
  intro Q _
  exact hG Q

/-! ### R20. `split_ifs` · goal with `if Q then a else b` → two goals, with `Q` / `¬Q` in context -/
example (Q : Prop) [Decidable Q] (a b : ℂ) (P : ℂ → Prop) (ha : P a) (hb : P b) :
    P (if Q then a else b) := by
  split_ifs
  exacts [ha, hb]

/-! ### R21. `Complex.normSq_neg`, `map_one` · goal: `normSq (-z)` → `normSq z`, `normSq 1` → `1` -/
example (P : ℝ → Prop) (h : P 1) : P (Complex.normSq (-1)) := by
  rw [Complex.normSq_neg]
  rw [map_one]
  exact h

/-! ### R22. `norm_num` on `normSq` of a numeral · closes it -/
example : Complex.normSq (1 / 3) = 1 / 9 := by norm_num

/-! ### R23. `one_mul` · `1 * a = a` · goal -/
example {α : Type} [MulOneClass α] (a : α) (P : α → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ### R24. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R25. `Finset.mul_sum` · `a * ∑ i, f i = ∑ i, a * f i` · goal: a factor moves into a sum -/
example {α : Type} [Fintype α] (a : ℝ) (f : α → ℝ) (P : ℝ → Prop) (h : P (∑ i, a * f i)) :
    P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R26. `Finset.sum_add_distrib` · `∑ (f i + g i) = ∑ f i + ∑ g i`; right to left merges sums -/
example {α : Type} [Fintype α] (f g : α → ℝ) (P : ℝ → Prop) (h : P (∑ i, (f i + g i))) :
    P (∑ i, f i + ∑ i, g i) := by
  rw [← Finset.sum_add_distrib]
  exact h

/-! ### R27. `refine Finset.sum_congr rfl fun r _ => ?_` · goal `∑ f = ∑ g` → `f r = g r` for one `r` -/
example {α : Type} [Fintype α] (f g : α → ℝ) (h : ∀ r, f r = g r) : ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun r _ => ?_
  exact h r

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A bit flip done twice: R6, R8, then `simp [name]` (R9–R11) -/
def flip1 (w : Fin 2 × ℕ → ℂ) : Fin 2 × ℕ → ℂ := fun q => w (q.1 + 1, q.2)
example (w : Fin 2 × ℕ → ℂ) : flip1 (flip1 w) = w := by
  funext ⟨c, n⟩
  fin_cases c
  all_goals simp [flip1]

/-! ### W2. The square-root milestone for `√3`: R1, R2, R3, R4, R5 -/
example : t * t = 1 / 3 := by
  rw [t]
  rw [← mul_inv]
  rw [← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (by norm_num)]
  norm_num

/-! ### W3. `t` twice in a product, separated by another factor: R13, then `simp [sq, h]`, then R15 -/
example (w : Fin 2 × ℕ → ℂ) (n : ℕ) (h : t * t = 1 / 3) : t * (w (0, n) * t) = 3⁻¹ * w (0, n) := by
  ring_nf
  simp [sq, h]
  ring

/-! ### W4. Sum bookkeeping: R16, R18, R22, R24, R25, R26, then R27 and R15 -/
example {α : Type} [Fintype α] (w : Fin 2 × α → ℂ) :
    ∑ q, Complex.normSq (3 * w q) = 9 * ∑ q, Complex.normSq (w q) := by
  have h9 : Complex.normSq 3 = 9 := by norm_num
  simp only [Fintype.sum_prod_type, Complex.normSq_mul, h9, Fin.sum_univ_two, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

end M132Guide

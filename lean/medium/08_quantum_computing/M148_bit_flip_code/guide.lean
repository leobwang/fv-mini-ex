/- Guide for M148 (Three-qubit bit-flip code).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (two bits instead of three, another
linear map).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M148Guide

/-! # Part R · Reference entries -/

/-! ## Brute force: functions on a finite set of labels -/

/-! ### R1. `funext ⟨a, b, c⟩` · goal `f = g` (functions on triples) → context gains `a b c`, goal one value -/
example {α β γ δ : Type} (f g : α × β × γ → δ) (h : ∀ a b c, f (a, b, c) = g (a, b, c)) :
    f = g := by
  funext ⟨a, b, c⟩
  exact h a b c

/-! ### R2. `rcases e with _ | e` · context loses `e : Option α`; goal → a `none` goal and a `some e` goal -/
example {α : Type} (P : Option α → Prop) (h0 : P none) (h1 : ∀ x, P (some x)) (e : Option α) :
    P e := by
  rcases e with _ | e
  exact h0
  exact h1 e

/-! ### R3. `fin_cases e` on `e : Fin 3` · context loses `e`; goal → three goals, one per value -/
example (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (e : Fin 3) : P e := by
  fin_cases e
  exacts [h0, h1, h2]

/-! ### R4. `all_goals (try t)` · goal list: `t` runs on every goal; where it fails the goal is kept
After R2 only the `some e` goal has an `e : Fin 3` to split; `try` skips the `none` goal. -/
example (P : Option (Fin 3) → Prop) (h0 : P none) (h1 : P (some 0)) (h2 : P (some 1))
    (h3 : P (some 2)) (e : Option (Fin 3)) : P e := by
  rcases e with _ | e
  all_goals (try fin_cases e)
  exacts [h0, h1, h2, h3]

/-! ### R5. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α × β → M) (P : M → Prop)
    (h : P (∑ x, ∑ y, f (x, y))) : P (∑ p, f p) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R6. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R7. `Finset.sum_apply` · goal: a sum of functions applied to a point → a sum of values -/
example {ι α β : Type} [AddCommMonoid β] (s : Finset ι) (g : ι → α → β) (a : α) (P : β → Prop)
    (h : P (∑ c ∈ s, g c a)) : P ((∑ c ∈ s, g c) a) := by
  rw [Finset.sum_apply]
  exact h

/-! ### R8. `simp` decides an `if` on concrete labels · goal: `if (1, 0) = (0, 0) then x else y` → `y` -/
example {β : Type} (x y : β) (P : β → Prop) (h : P y) :
    P (if ((1 : Fin 2), (0 : Fin 2)) = (0, 0) then x else y) := by
  simp
  exact h

/-! ### R9. `simp` computes in `Fin 2` · goal: `1 + 1` → `0` (`+` on `Fin 2` is XOR) -/
example (P : Fin 2 → Prop) (h : P 0) : P ((1 : Fin 2) + 1) := by
  simp
  exact h

/-! ## Linearity: moving scalars and sums around -/

/-! ### R10. `Pi.smul_apply` · goal: `(b • x) i` → `b • x i` (scalar times a function, at a point) -/
example {ι M α : Type} [SMul M α] (b : M) (x : ι → α) (i : ι) (P : α → Prop) (h : P (b • x i)) :
    P ((b • x) i) := by
  rw [Pi.smul_apply]
  exact h

/-! ### R11. `smul_eq_mul` · goal: `a • b` → `a * b` when both live in the same ring -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R12. `Finset.mul_sum` · goal: `a * ∑ i ∈ s, f i` → `∑ i ∈ s, a * f i` -/
example {ι α : Type} [NonUnitalNonAssocSemiring α] (s : Finset ι) (a : α) (f : ι → α)
    (P : α → Prop) (h : P (∑ i ∈ s, a * f i)) : P (a * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R13. `simp_rw [l]` · goal: rewrites with `l` also under binders (`fun x => …`, `∑ x, …`)
Here the factor `a i` mentions the bound `i`, so `rw [Finset.mul_sum]` fails ("did not find an
occurrence of the pattern": `rw` cannot look under a binder); `simp_rw` rewrites inside the binder.
Bound variables may be renamed in the result (`i` → `x`); that is only printing. -/
example {ι κ α : Type} [NonUnitalNonAssocSemiring α] (s : Finset ι) (t : Finset κ) (a : ι → α)
    (f : ι → κ → α) (P : α → Prop) (h : P (∑ i ∈ s, ∑ j ∈ t, a i * f i j)) :
    P (∑ i ∈ s, a i * ∑ j ∈ t, f i j) := by
  simp_rw [Finset.mul_sum]
  exact h

/-! ### R14. `mul_ite` · goal: `a * (if c then b else d)` → `if c then a * b else a * d` -/
example {α : Type} [Mul α] (c : Prop) [Decidable c] (a b d : α) (P : α → Prop)
    (h : P (if c then a * b else a * d)) : P (a * if c then b else d) := by
  rw [mul_ite]
  exact h

/-! ### R15. `mul_zero` · goal: `a * 0` → `0` -/
example {α : Type} [MulZeroClass α] (a : α) (P : α → Prop) (h : P 0) : P (a * 0) := by
  rw [mul_zero]
  exact h

/-! ### R16. `Finset.sum_comm` · goal: swap the order of a double sum -/
example {ι κ M : Type} [AddCommMonoid M] (s : Finset ι) (t : Finset κ) (f : ι → κ → M)
    (P : M → Prop) (h : P (∑ j ∈ t, ∑ i ∈ s, f i j)) : P (∑ i ∈ s, ∑ j ∈ t, f i j) := by
  rw [Finset.sum_comm]
  exact h

/-! ### R17. `refine Finset.sum_congr rfl fun i hi => ?_` · goal: `∑ = ∑` → one term, context gains `i, hi` -/
example {ι M : Type} [AddCommMonoid M] (s : Finset ι) (f g : ι → M) (h : ∀ i ∈ s, f i = g i) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  exact h i hi

/-! ### R18. `split_ifs with hc` · goal with `if c` → goal list: one goal with `hc : c`, one with `hc : ¬c` -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hx : c → P x)
    (hy : ¬c → P y) : P (if c then x else y) := by
  split_ifs with hc
  exact hx hc
  exact hy hc

/-! ### R19. `Finset.sum_smul` · goal: `(∑ i ∈ s, r i) • x` → `∑ i ∈ s, r i • x` -/
example {ι R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] (s : Finset ι) (r : ι → R)
    (x : M) (P : M → Prop) (h : P (∑ i ∈ s, r i • x)) : P ((∑ i ∈ s, r i) • x) := by
  rw [Finset.sum_smul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Brute force on two bits: R1, R2, R4, then `fin_cases` + `simp` (R5–R9)
`fl e` flips bit `e` of a two-bit label (`none` = no flip). Flipping twice is the identity. -/
def fl : Option (Fin 2) → Fin 2 × Fin 2 → Fin 2 × Fin 2
  | none, p => p
  | some 0, p => (p.1 + 1, p.2)
  | some 1, p => (p.1, p.2 + 1)

example (e : Option (Fin 2)) : (fun p => fl e (fl e p)) = fun p => p := by
  funext ⟨a, b⟩
  rcases e with _ | e
  all_goals (try fin_cases e)
  all_goals (fin_cases a <;> fin_cases b <;> simp [fl])

/-! ### W2. A finite sum of values over pairs: R5, R6, then `simp` evaluates each `if` (R8, R9) -/
example (x : ℂ) : ∑ p : Fin 2 × Fin 2, (if p.1 + p.2 = 1 then x else 0) = x + x := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

/-! ### W3. Linearity of a sum-of-functions map: R1 (as `funext p`), R7, R10, R11, R13–R18 -/
def L (v : Fin 2 → ℂ) : Fin 2 → ℂ := ∑ σ : Fin 2, fun p => if p = σ then v (p + 1) else 0

example {ι : Type} [Fintype ι] (c : ι → ℂ) (v : ι → Fin 2 → ℂ) :
    L (∑ e, c e • v e) = ∑ e, c e • L (v e) := by
  funext p
  simp only [L, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> simp

end M148Guide

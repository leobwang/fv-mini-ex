/- Guide for H097 (Transfer matrix of the Ising ring).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders, in the order the skeletons use them. Put the cursor before and after the step to see
the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (paths of length 2, other sums).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H097Guide

/-! # Part R · Reference entries -/

/-! ## Path sums, base case: induction, `M ^ 0`, sums over `Fin 1 → β` -/

/-! ### R1. `induction n generalizing a with` · goal list: base case and step; the step's
hypothesis `ih` holds for EVERY `a`, not just the fixed one -/
example (P : ℕ → Bool → Prop) (h0 : ∀ a, P 0 a) (hs : ∀ n, (∀ a, P n a) → ∀ a, P (n + 1) a)
    (n : ℕ) (a : Bool) : P n a := by
  induction n generalizing a with
    | zero => exact h0 a
    | succ n ih => exact hs n ih a

/-- The same split, unfolded so the infoview shows the two goals. Without `with`, the new names
print as `n✝`, `a✝`; `rename_i n ih` gives them the names `| succ n ih =>` would. -/
example (P : ℕ → Bool → Prop) (h0 : ∀ a, P 0 a) (hs : ∀ n, (∀ a, P n a) → ∀ a, P (n + 1) a)
    (n : ℕ) (a : Bool) : P n a := by
  induction n generalizing a
  case zero => exact h0 a
  rename_i n ih
  exact hs n ih a

/-! ### R2. `pow_zero` · `x ^ 0 = 1` · goal -/
example {α : Type} [Monoid α] (x : α) (P : α → Prop) (h : P 1) : P (x ^ 0) := by
  rw [pow_zero]
  exact h

/-! ### R3. `Matrix.one_apply` · goal: an entry of the identity matrix → an `if` -/
example {α : Type} [Zero α] [One α] (a b : Bool) (P : α → Prop) (h : P (if a = b then 1 else 0)) :
    P ((1 : Matrix Bool Bool α) a b) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R4. `Equiv.sum_comp` · `∑ i, g (e i) = ∑ k, g k` for `e : ι ≃ κ`; right to left
it turns a sum over `κ` into a sum over `ι` · goal -/
example {ι κ M : Type} [Fintype ι] [Fintype κ] [AddCommMonoid M] (e : ι ≃ κ) (g : κ → M)
    (P : M → Prop) (h : P (∑ i, g (e i))) : P (∑ k, g k) := by
  rw [← e.sum_comp]
  exact h

/-! ### R5. `Equiv.funUnique (Fin 1) β` · `(Fin 1 → β) ≃ β`; its inverse sends `b` to the
constant function: `Equiv.funUnique_symm_apply`, then `uniqueElim_const` · goal -/
example {β : Type} (b : β) (P : β → Prop) (h : P b) :
    P ((Equiv.funUnique (Fin 1) β).symm b 0) := by
  rw [Equiv.funUnique_symm_apply]
  rw [uniqueElim_const]
  exact h

/-! ### R6. `cases a <;> cases b` (`a b : Bool`) · goal list: one goal per pair of values -/
example (P : Bool → Bool → Prop) (h1 : P false false) (h2 : P false true) (h3 : P true false)
    (h4 : P true true) (a b : Bool) : P a b := by
  cases a <;> cases b
  exacts [h1, h2, h3, h4]

/-! ### R7. `simp [Fin.last]` · goal: `Fin.last 0` is the index `⟨0, ⋯⟩`, which `simp` reads as `0` -/
example {β : Type} (f : Fin 1 → β) (P : β → Prop) (h : P (f 0)) : P (f (Fin.last 0)) := by
  simp only [Fin.last]
  exact h

/-! ## Path sums, step: split a path into its first spin and the rest -/

/-! ### R8. `Fin.consEquiv fun _ => β` · `β × (Fin n → β) ≃ (Fin (n + 1) → β)`: a first value and
the rest. With R4 it turns a sum over paths into a sum over pairs · goal -/
example {β M : Type} [Fintype β] [AddCommMonoid M] (n : ℕ) (g : (Fin (n + 1) → β) → M)
    (P : M → Prop) (h : P (∑ p : β × (Fin n → β), g ((Fin.consEquiv fun _ => β) p))) :
    P (∑ σ, g σ) := by
  rw [← (Fin.consEquiv fun _ => β).sum_comp]
  exact h

/-! ### R9. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {β γ M : Type} [Fintype β] [Fintype γ] [AddCommMonoid M] (f : β × γ → M) (P : M → Prop)
    (h : P (∑ x, ∑ y, f (x, y))) : P (∑ p, f p) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R10. `Finset.sum_comm` · goal: swap the order of a double sum -/
example {β γ M : Type} [Fintype β] [Fintype γ] [AddCommMonoid M] (f : β → γ → M) (P : M → Prop)
    (h : P (∑ y, ∑ x, f x y)) : P (∑ x, ∑ y, f x y) := by
  rw [Finset.sum_comm]
  exact h

/-! ### R11. `refine Finset.sum_congr rfl fun i _ => ?_` · goal: equal sums → equal summands;
context gains `i` and `x✝ : i ∈ Finset.univ` -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M) (hfg : ∀ i, f i = g i) :
    ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hfg i

/-! ### R12. `Fin.consEquiv_apply` · goal: `(Fin.consEquiv _) (x, τ)` → `Fin.cons x τ`
`rw` leaves the projections `(x, τ).1`, `(x, τ).2`; `simp only` also reduces them. -/
example {β : Type} (n : ℕ) (x : β) (τ : Fin n → β) (P : β → Prop)
    (h : P ((Fin.cons x τ : Fin (n + 1) → β) 0)) :
    P ((Fin.consEquiv fun _ => β) (x, τ) 0) := by
  simp only [Fin.consEquiv_apply]
  exact h

/-! ### R13. `Fin.cons_zero`, `Fin.cons_succ` · goal: `Fin.cons x τ 0 = x`, `Fin.cons x τ i.succ = τ i` -/
example {β : Type} (n : ℕ) (x : β) (τ : Fin n → β) (i : Fin n) (P : β → β → Prop)
    (h : P x (τ i)) :
    P ((Fin.cons x τ : Fin (n + 1) → β) 0) ((Fin.cons x τ : Fin (n + 1) → β) i.succ) := by
  rw [Fin.cons_zero]
  rw [Fin.cons_succ]
  exact h

/-! ### R14. `Fin.succ_last`, `Fin.succ_castSucc`, `Fin.castSucc_zero` · goal: rewrite an index
so that R13 applies. `(Fin.last n).succ = Fin.last (n + 1)` and `i.castSucc.succ = i.succ.castSucc`
are used right to left; `Fin.castSucc 0 = 0` left to right. -/
example {β : Type} (n : ℕ) (x : β) (τ : Fin (n + 1) → β) (P : β → Prop)
    (h : P ((Fin.cons x τ : Fin (n + 2) → β) (Fin.last n).succ)) :
    P ((Fin.cons x τ : Fin (n + 2) → β) (Fin.last (n + 1))) := by
  rw [← Fin.succ_last]
  exact h

example {β : Type} (n : ℕ) (x : β) (τ : Fin (n + 1) → β) (i : Fin n) (P : β → Prop)
    (h : P ((Fin.cons x τ : Fin (n + 2) → β) i.castSucc.succ)) :
    P ((Fin.cons x τ : Fin (n + 2) → β) i.succ.castSucc) := by
  rw [← Fin.succ_castSucc]
  exact h

example {β : Type} (n : ℕ) (f : Fin (n + 2) → β) (P : β → Prop) (h : P (f 0)) :
    P (f (Fin.castSucc 0)) := by
  rw [Fin.castSucc_zero]
  exact h

/-! ### R15. `Fin.prod_univ_succ` · goal: a product over `Fin (n + 1)` → first factor times the rest -/
example {M : Type} [CommMonoid M] (n : ℕ) (f : Fin (n + 1) → M) (P : M → Prop)
    (h : P (f 0 * ∏ i : Fin n, f i.succ)) : P (∏ i, f i) := by
  rw [Fin.prod_univ_succ]
  exact h

/-! ### R16. `Finset.sum_eq_single a` · goal list: the sum → its `a` term, plus two side goals
(every other term is `0`; the case `a ∉ s`, trivial for `Finset.univ`) -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (f : ι → M) (a : ι) (P : M → Prop)
    (h : P (f a)) (h0 : ∀ b ∈ Finset.univ, b ≠ a → f b = 0) (h1 : a ∉ Finset.univ → f a = 0) :
    P (∑ x, f x) := by
  rw [Finset.sum_eq_single a]
  exacts [h, h0, h1]

/-! ## Path sums, step: `M ^ (n + 1) = M * M ^ n` and the induction hypothesis -/

/-! ### R17. `pow_succ'` · `x ^ (n + 1) = x * x ^ n` (peel the FIRST factor) · goal -/
example {α : Type} [Monoid α] (x : α) (n : ℕ) (P : α → Prop) (h : P (x * x ^ n)) :
    P (x ^ (n + 1)) := by
  rw [pow_succ']
  exact h

/-! ### R18. `Matrix.mul_apply` · goal: an entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix Bool Bool α) (a b : Bool)
    (P : α → Prop) (h : P (∑ j, M a j * N j b)) : P ((M * N) a b) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R19. `simp_rw [hfg]` · goal: rewrite UNDER a binder (`∑ i, …`, `fun i => …`), where `rw`
cannot reach because `i` is bound -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M) (hfg : ∀ i, f i = g i)
    (P : M → Prop) (h : P (∑ i, g i)) : P (∑ i, f i) := by
  simp_rw [hfg]
  exact h

/-! ### R20. `Finset.mul_sum` · `a * ∑ i, f i = ∑ i, a * f i` · goal -/
example {ι R : Type} [Fintype ι] [CommSemiring R] (a : R) (f : ι → R) (P : R → Prop)
    (h : P (∑ i, a * f i)) : P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R21. `by_cases hb : p` · goal list: one goal with `hb : p`, one with `hb : ¬p` -/
example (p G : Prop) (hp : p → G) (hn : ¬p → G) : G := by
  by_cases hb : p
  exacts [hp hb, hn hb]

/-! ### R22. `Ne.symm` · `c ≠ d → d ≠ c` · context gains the flipped fact
`simp [hc]` with `hc : c ≠ d` simplifies `c = d` to `False` but not `d = c`. -/
example {β : Type} (c d : β) (hc : c ≠ d) (G : Prop) (g : d ≠ c → G) : G := by
  have hd := Ne.symm hc
  exact g hd

/-! ## Trace of a power -/

/-! ### R23. `Matrix.trace`, then `Matrix.diag` · goal: trace → sum of diagonal entries -/
example {α : Type} [AddCommMonoid α] (M : Matrix Bool Bool α) (P : α → Prop)
    (h : P (∑ i, M i i)) : P M.trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag]
  exact h

/-! ### R24. `pow_succ` · `x ^ (n + 1) = x ^ n * x` (peel the LAST factor) · goal -/
example {α : Type} [Monoid α] (x : α) (n : ℕ) (P : α → Prop) (h : P (x ^ n * x)) :
    P (x ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R25. `Finset.sum_mul` · `(∑ i, f i) * a = ∑ i, f i * a` · goal -/
example {ι R : Type} [Fintype ι] [CommSemiring R] (a : R) (f : ι → R) (P : R → Prop)
    (h : P (∑ i, f i * a)) : P ((∑ i, f i) * a) := by
  rw [Finset.sum_mul]
  exact h

/-! ### R26. `ite_mul`, then `zero_mul` · goal: push `* c` into both branches of an `if` -/
example {α : Type} [MulZeroClass α] (p : Prop) [Decidable p] (a c : α) (P : α → Prop)
    (h : P (if p then a * c else 0)) : P ((if p then a else 0) * c) := by
  rw [ite_mul]
  rw [zero_mul]
  exact h

/-! ### R27. `ite_and` · goal: `if p ∧ q` → two nested `if`s -/
example {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b : α) (P : α → Prop)
    (h : P (if p then if q then a else b else b)) : P (if p ∧ q then a else b) := by
  rw [ite_and]
  exact h

/-! ### R28. `Finset.sum_ite_eq` · `∑ x ∈ s, (if a = x then f x else 0) = if a ∈ s then f a else 0`
· goal; `simp` applies it (and `Finset.mem_univ`) by itself -/
example {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (a : ι) (f : ι → M)
    (P : M → Prop) (h : P (if a ∈ Finset.univ then f a else 0)) :
    P (∑ x, if a = x then f x else 0) := by
  rw [Finset.sum_ite_eq]
  exact h

/-! ## Sharing the field term: peeling sums over `Fin (n + 1)` -/

/-! ### R29. `Fin.sum_univ_castSucc` · goal: peel the LAST term of a sum over `Fin (n + 1)`
As a fact instead: `have h1 := Fin.sum_univ_castSucc f` (W5). -/
example {M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M) (P : M → Prop)
    (h : P (∑ i : Fin n, f i.castSucc + f (Fin.last n))) : P (∑ i, f i) := by
  rw [Fin.sum_univ_castSucc]
  exact h

/-! ### R30. `Fin.sum_univ_succ` · goal: peel the FIRST term of a sum over `Fin (n + 1)`
As a fact instead: `have h2 := Fin.sum_univ_succ f` (W5). -/
example {M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M) (P : M → Prop)
    (h : P (f 0 + ∑ i : Fin n, f i.succ)) : P (∑ i, f i) := by
  rw [Fin.sum_univ_succ]
  exact h

/-! ### R31. `Finset.sum_div` · `(∑ i, f i) / a = ∑ i, f i / a`; right to left it pulls `/ a` out · goal -/
example {ι K : Type} [Fintype ι] [DivisionSemiring K] (f : ι → K) (a : K) (P : K → Prop)
    (h : P ((∑ i, f i) / a)) : P (∑ i, f i / a) := by
  rw [← Finset.sum_div]
  exact h

/-! ### R32. `Finset.sum_add_distrib` · `∑ i, (f i + g i) = ∑ i, f i + ∑ i, g i` · goal -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M) (P : M → Prop)
    (h : P (∑ i, f i + ∑ i, g i)) : P (∑ i, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R33. `linarith` · closes a linear (in)equality over `ℝ` from the hypotheses; any
non-linear subterm, such as `∑ i, f i`, is treated as one unknown -/
example (s x y : ℝ) (h1 : s = x + y) (h2 : s = 2 * y) : s = (x + y) / 2 + y := by
  linarith

/-! ## The Boltzmann weight as a product of matrix entries -/

/-! ### R34. `Matrix.of_apply` · goal: an entry of `Matrix.of f` → `f` applied -/
example {α : Type} (f : Bool → Bool → α) (a b : Bool) (P : α → Prop) (h : P (f a b)) :
    P (Matrix.of f a b) := by
  rw [Matrix.of_apply]
  exact h

/-! ### R35. `Real.exp_sum` · `exp (∑ i, f i) = ∏ i, exp (f i)`; right to left it merges a product · goal -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (P : ℝ → Prop) (h : P (Real.exp (∑ i, f i))) :
    P (∏ i, Real.exp (f i)) := by
  rw [← Real.exp_sum]
  exact h

/-! ### R36. `Real.exp_add` · `exp (x + y) = exp x * exp y`; right to left it merges two factors · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x + y))) : P (Real.exp x * Real.exp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R37. `congr 1` · goal `f x = f y` → `x = y` (strip one function application) -/
example (x : ℝ) : Real.exp (x + 0) = Real.exp x := by
  congr 1
  exact add_zero x

/-! ### R38. `simp only [mul_add, mul_neg, neg_mul, sub_eq_add_neg]` · goal: distribute `*` over
`+` and pull every `-` outward, so the sums become separate summands -/
example {R : Type} [CommRing R] (a b c : R) (P : R → Prop) (h : P (-(a * b) + - -(a * c))) :
    P (-a * (b - c)) := by
  simp only [mul_add, mul_neg, neg_mul, sub_eq_add_neg]
  exact h

/-! ### R39. `ring_nf`, `ring` with sums · `ring` treats `∑ i, f i` as one unknown; `ring_nf`
also normalises each summand INSIDE the sum -/
example {ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, f i * a * 2)) :
    P (∑ i, 2 * (f i * a)) := by
  ring_nf
  exact h

example {ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    (a * ∑ i, f i) * 2 = 2 * a * ∑ i, f i := by ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A path of length 2: R17, then `pow_one : x ^ 1 = x`, then R18 -/
example (M : Matrix Bool Bool ℝ) (a b : Bool) : (M ^ 2) a b = ∑ j, M a j * M j b := by
  rw [pow_succ']
  rw [pow_one]
  rw [Matrix.mul_apply]

/-! ### W2. The trace of a product: R23, then R18 under the binder (R19) -/
example (M N : Matrix Bool Bool ℝ) : (M * N).trace = ∑ i, ∑ j, M i j * N j i := by
  rw [Matrix.trace]
  simp only [Matrix.diag]
  simp_rw [Matrix.mul_apply]

/-! ### W3. Split a sum over `Fin (n + 1) → Bool` into first value and the rest: R8, R9, R12, R13 -/
example (n : ℕ) (f : Bool → ℝ) (g : (Fin n → Bool) → ℝ) :
    ∑ σ : Fin (n + 1) → Bool, f (σ 0) * g (fun i => σ i.succ) = ∑ x, ∑ τ, f x * g τ := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]

/-! ### W4. Collapse a sum to one term: R16, then each of the three goals; R22 flips `hx` -/
example (f : Bool → ℝ) (c : Bool) : ∑ x, (if c = x then f x else 0) = f c := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-! ### W5. Peel both ends and let `linarith` combine: R29, R30, R33 -/
example (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, f i.succ - ∑ i : Fin n, f i.castSucc = f (Fin.last n) - f 0 := by
  have h1 := Fin.sum_univ_castSucc f
  have h2 := Fin.sum_univ_succ f
  linarith

/-! ### W6. A product of exponentials as one exponential: R35, R36, then R37 -/
example (n : ℕ) (v : Fin n → ℝ) (y : ℝ) :
    (∏ i, Real.exp (v i)) * Real.exp y = Real.exp (y + ∑ i, v i) := by
  rw [← Real.exp_sum]
  rw [← Real.exp_add]
  congr 1
  ring

/-! ### W7. Reorder a triple sum with a `calc`: R10 under the outer sum (R11, as a term), then R10.
The first step names its middle expression; the second `_ = _` lets Lean fill it in. -/
example (f : Bool → Bool → Fin 3 → ℝ) :
    ∑ a, ∑ b, ∑ k, f a b k = ∑ k, ∑ a, ∑ b, f a b k := by
  calc _ = ∑ a, ∑ k, ∑ b, f a b k := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

end H097Guide

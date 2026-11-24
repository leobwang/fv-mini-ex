/- Guide for H096 (Spin correlations in the Ising chain).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other sums over spin chains,
another `n`-independent quantity, `tanh ^ 3`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H096Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Appending a site: `Fin.castSucc`, `Fin.succ`, `Fin.last`, `Fin.snoc` -/

/-! ### R1. `Fin.sum_univ_castSucc` · goal: a sum over `Fin (n + 1)` → the first `n` terms + the last -/
example {M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M) (P : M → Prop)
    (h : P (∑ i : Fin n, f i.castSucc + f (Fin.last n))) : P (∑ i, f i) := by
  rw [Fin.sum_univ_castSucc]
  exact h

/-! ### R2. `simp only [Fin.succ_castSucc]` · goal: `i.castSucc.succ` → `i.succ.castSucc`, also
under `∑ i` (there `rw` fails: the pattern mentions the bound variable `i`) -/
example {M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 2) → M) (P : M → Prop)
    (h : P (∑ i : Fin n, f i.succ.castSucc)) : P (∑ i : Fin n, f i.castSucc.succ) := by
  simp only [Fin.succ_castSucc]
  exact h

/-! ### R3. `Fin.snoc_castSucc` · goal: `Fin.snoc p x` at an old site `i.castSucc` → `p i` -/
example {α : Type} (n : ℕ) (p : Fin (n + 1) → α) (x : α) (i : Fin (n + 1)) (P : α → Prop)
    (h : P (p i)) : P ((Fin.snoc p x : Fin (n + 2) → α) i.castSucc) := by
  simp only [Fin.snoc_castSucc]
  exact h

/-! ### R4. `simp only [Fin.succ_last]` · goal: `(Fin.last n).succ` → `Fin.last (n + 1)` -/
example (n : ℕ) (P : Fin (n + 2) → Prop) (h : P (Fin.last (n + 1))) : P (Fin.last n).succ := by
  simp only [Fin.succ_last]
  exact h

/-! ### R5. `Fin.snoc_last` · goal: `Fin.snoc p x` at the new last site → `x` -/
example {α : Type} (n : ℕ) (p : Fin (n + 1) → α) (x : α) (P : α → Prop) (h : P x) :
    P ((Fin.snoc p x : Fin (n + 2) → α) (Fin.last (n + 1))) := by
  simp only [Fin.snoc_last]
  exact h

/-! ## Part 1 · Re-indexing the sum over configurations -/

/-! ### R6. `Fin.snocEquiv` with `Equiv.sum_comp`, right to left · goal: sum over `Fin (n + 2) → α`
→ sum over pairs `(last value, first n + 1 values)` -/
example {α M : Type} [Fintype α] [AddCommMonoid M] (n : ℕ)
    (F : (Fin (n + 2) → α) → M) (P : M → Prop)
    (h : P (∑ p : α × (Fin (n + 1) → α), F ((Fin.snocEquiv fun _ => α) p))) : P (∑ σ, F σ) := by
  rw [← (Fin.snocEquiv fun _ => α).sum_comp]
  exact h

/-! ### R7. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α × β → M) (P : M → Prop)
    (h : P (∑ a, ∑ b, F (a, b))) : P (∑ p, F p) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R8. `Finset.sum_comm` · goal: swap the order of a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α → β → M) (P : M → Prop)
    (h : P (∑ b, ∑ a, F a b)) : P (∑ a, ∑ b, F a b) := by
  rw [Finset.sum_comm]
  exact h

/-! ### R9. `refine Finset.sum_congr rfl fun x _ => ?_` · goal: `∑ f = ∑ g` → `f x = g x`;
context gains `x` and `x✝ : x ∈ Finset.univ` -/
example {α M : Type} [Fintype α] [AddCommMonoid M] (f g : α → M) (h : ∀ a, f a = g a) :
    ∑ a, f a = ∑ a, g a := by
  refine Finset.sum_congr rfl fun x _ => ?_
  exact h x

/-! ### R10. `Finset.sum_mul` · goal: `(∑ i, f i) * a` → `∑ i, f i * a` -/
example {α R : Type} [Fintype α] [Semiring R] (f : α → R) (a : R) (P : R → Prop)
    (h : P (∑ i, f i * a)) : P ((∑ i, f i) * a) := by
  rw [Finset.sum_mul]
  exact h

/-! ### R11. `show` · goal: `(Fin.snocEquiv _) (x, p)` → the same value written `Fin.snoc p x` -/
example {α : Type} (n : ℕ) (x : α) (p : Fin (n + 1) → α) (Q : (Fin (n + 2) → α) → Prop)
    (h : Q (Fin.snoc p x)) : Q ((Fin.snocEquiv fun _ => α) (x, p)) := by
  show Q (Fin.snoc p x : Fin (n + 2) → α)
  exact h

/-! ### R12. `mul_assoc` · goal: `a * b * c` → `a * (b * c)` -/
example {α : Type} [Semigroup α] (a b c : α) (P : α → Prop) (h : P (a * (b * c))) :
    P (a * b * c) := by
  rw [mul_assoc]
  exact h

/-! ### R13. `Real.exp_add`, right to left · goal: `exp x * exp y` → `exp (x + y)` -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x + y))) : P (Real.exp x * Real.exp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R14. `ring_nf` · closes a goal that is a ring identity only after normalizing the
arguments of `Real.exp`; plain `ring` treats `exp (a - b)` and `exp (-b + a)` as different atoms -/
example (a b c : ℝ) : c * Real.exp (a - b) = Real.exp (-b + a) * c := by ring_nf

/-! ## Part 2 · Summing out one spin: sums over `Bool`, `cosh`, `sinh` -/

/-! ### R15. `cases b` (for `b : Bool`) · goal list: `P b` → `P false`, `P true` -/
example (P : Bool → Prop) (hf : P false) (ht : P true) (b : Bool) : P b := by
  cases b
  exacts [hf, ht]

/-! ### R16. `rcases hs with rfl | rfl` · context loses `hs : s = 1 ∨ s = -1` and `s`;
goal list: `P s` → `P 1`, `P (-1)` -/
example (s : ℝ) (P : ℝ → Prop) (h1 : P 1) (h2 : P (-1)) (hs : s = 1 ∨ s = -1) : P s := by
  rcases hs with rfl | rfl
  exacts [h1, h2]

/-! ### R17. `Fintype.sum_bool` · goal: `∑ b : Bool, f b` → `f true + f false` -/
example {M : Type} [AddCommMonoid M] (f : Bool → M) (P : M → Prop) (h : P (f true + f false)) :
    P (∑ b, f b) := by
  rw [Fintype.sum_bool]
  exact h

/-! ### R18. `Real.cosh_eq` · goal: `cosh x` → `(exp x + exp (-x)) / 2` -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((Real.exp x + Real.exp (-x)) / 2)) : P (Real.cosh x) := by
  rw [Real.cosh_eq]
  exact h

/-! ### R19. `Real.sinh_eq` · goal: `sinh x` → `(exp x - exp (-x)) / 2` -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((Real.exp x - Real.exp (-x)) / 2)) : P (Real.sinh x) := by
  rw [Real.sinh_eq]
  exact h

/-! ### R20. `rw [L (fun a _ => g a)]` · goal: rewrite with a lemma about every `f`, after choosing
`f`; Lean beta-reduces `(fun a _ => g a) a true` to `g a` before matching -/
example {α : Type} [Fintype α] (L : ∀ f : α → Bool → ℝ, ∑ a, f a true = ∑ a, ∑ b, f a b)
    (g : α → ℝ) (P : ℝ → Prop) (h : P (∑ a, ∑ _b : Bool, g a)) : P (∑ a, g a) := by
  rw [L (fun a _ => g a)]
  exact h

/-! ### R21. `Finset.mul_sum` · goal: `a * ∑ i, f i` → `∑ i, a * f i` (`←` pulls `a` back out) -/
example {α R : Type} [Fintype α] [Semiring R] (f : α → R) (a : R) (P : R → Prop)
    (h : P (∑ i, a * f i)) : P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ## Part 3 · Induction on the length: base case, specializing, folding -/

/-! ### R22. `Fin.sum_univ_zero` · goal: a sum over `Fin 0` (no bonds) → `0` -/
example {M : Type} [AddCommMonoid M] (f : Fin 0 → M) (P : M → Prop) (h : P 0) : P (∑ i, f i) := by
  rw [Fin.sum_univ_zero]
  exact h

/-! ### R23. `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fun` · goal: a constant sum over
all `σ : Fin 1 → Bool` → (number of `σ`) • `c`; `simp` finishes `2 ^ 1 • c` to `2 * c` -/
example (c : ℝ) (P : ℝ → Prop) (h : P (2 * c)) : P (∑ _σ : Fin 1 → Bool, c) := by
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [Fintype.card_fun]
  simp
  exact h

/-! ### R24. `simp only [one_mul] at h` · context: `h` rewritten (also under `∑`), goal unchanged -/
example (a : ℝ) (P : ℝ → Prop) (h : P (1 * a)) : P a := by
  simp only [one_mul] at h
  exact h

/-! ### R25. `rw [D]` unfolds a definition, `rw [← D]` folds its body back into the name · goal -/
def T (n : ℕ) : ℕ := 2 ^ n

example (n : ℕ) (P : ℕ → Prop) (e : 2 ^ (n + 1) = 2 ^ n * 2) (h : P (T n * 2)) : P (T (n + 1)) := by
  rw [T]
  rw [e]
  rw [← T]
  exact h

/-! ## Part 4 · The end-to-end numerator -/

/-! ### R26. `Fin.castSucc_zero` · context (`at h`): `Fin.castSucc 0` → `0` -/
example (n : ℕ) (P : Fin (n + 2) → Prop) (h : P (Fin.castSucc (0 : Fin (n + 1)))) : P 0 := by
  simp only [Fin.castSucc_zero] at h
  exact h

/-! ### R27. `pow_succ` · goal: `a ^ (n + 1)` → `a ^ n * a` -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R28. `simp_rw` · goal: rewrite UNDER a binder (inside `∑ b, …`), where `rw` cannot -/
example (c : ℝ) (f g : Bool → ℝ) (P : ℝ → Prop) (h : P (c * ∑ b, f b * g b)) :
    P (∑ b, c * f b * g b) := by
  simp_rw [mul_assoc c]
  simp_rw [← Finset.mul_sum]
  exact h

/-! ## Part 5 · Adding a spin far away changes nothing -/

/-! ### R29. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from positive pieces -/
example (x : ℝ) : 0 < 3 * Real.cosh x * Real.exp x := by positivity

/-! ### R30. `mul_div_mul_left` · `c ≠ 0 → c * a / (c * b) = a / b` · goal: cancel a common left factor -/
example (a b c : ℝ) (hc : c ≠ 0) (P : ℝ → Prop) (h : P (a / b)) : P (c * a / (c * b)) := by
  rw [mul_div_mul_left _ _ hc]
  exact h

/-! ## Part 6 · The main theorem -/

/-! ### R31. `induction n, hr using Nat.le_induction` · goal list: `Q n` (with `hr : r ≤ n`)
→ `Q r`, and `Q (n + 1)` with `hrn : r ≤ n`, `ih : Q n`.
`rename_i n hrn ih` names the new variables here; in a proof write
`induction n, hr using Nat.le_induction with | base => … | succ n hrn ih => …` (W3). -/
example (r : ℕ) (Q : ℕ → Prop) (h0 : Q r) (hs : ∀ n, r ≤ n → Q n → Q (n + 1)) (n : ℕ)
    (hr : r ≤ n) : Q n := by
  induction n, hr using Nat.le_induction
  · exact h0
  rename_i n hrn ih
  exact hs n hrn ih

/-! ### R32. `rw [show a = b from rfl]` · goal: replace `a` by a definitionally equal `b`
(here the index `⟨r, _⟩ : Fin (r + 1)` by `Fin.last r`, so a lemma about `Fin.last` applies) -/
example (r : ℕ) (P : Fin (r + 1) → Prop) (h : P (Fin.last r)) : P ⟨r, by omega⟩ := by
  rw [show (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r from rfl]
  exact h

/-! ### R33. `Real.tanh_eq_sinh_div_cosh` · goal: `tanh x` → `sinh x / cosh x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (Real.sinh x / Real.cosh x)) : P (Real.tanh x) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact h

/-! ### R34. `div_pow` · goal: `(a / b) ^ k` → `a ^ k / b ^ k` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (k : ℕ) (P : α → Prop) (h : P (a ^ k / b ^ k)) :
    P ((a / b) ^ k) := by
  rw [div_pow]
  exact h

/-! ### R35. `Real.cosh_pos` · `0 < cosh x` · context gains `hc : 0 < Real.cosh x` -/
example (x : ℝ) (G : Prop) (g : 0 < Real.cosh x → G) : G := by
  have hc := Real.cosh_pos x
  exact g hc

/-! ### R36. `field_simp` · goal: multiplies out every denominator it can prove nonzero
(it uses `0 < c` or `c ≠ 0` from the context) -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c = b) : a = b / c := by
  field_simp
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Re-index, split, and sum out the last site of an observable that ignores it:
R6, R7, R8, R21, R9, R17, R11, R3, then `ring` -/
example (n : ℕ) (g : (Fin (n + 1) → Bool) → ℝ) :
    ∑ σ : Fin (n + 2) → Bool, g (fun i => σ i.castSucc) = 2 * ∑ τ, g τ := by
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_bool]
  show g (fun i => (Fin.snoc τ true : Fin (n + 2) → Bool) i.castSucc) +
      g (fun i => (Fin.snoc τ false : Fin (n + 2) → Bool) i.castSucc) = 2 * g τ
  simp only [Fin.snoc_castSucc]
  ring

/-! ### W2. A `±1` variable and a two-term `Bool` sum: R16, R17, R18 -/
example (s : ℝ) (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

example (K : ℝ) : ∑ b : Bool, Real.exp (if b then K else -K) = 2 * Real.cosh K := by
  simp [Real.cosh_eq]
  ring

/-! ### W3. A quantity that stops depending on `n` once `n ≥ r`: R31 in the `with` form
(alternatives indented under `induction`) -/
example (f : ℕ → ℝ) (hf : ∀ n, f (n + 1) = f n) (r n : ℕ) (hr : r ≤ n) : f n = f r := by
  induction n, hr using Nat.le_induction with
    | base => rfl
    | succ n hrn ih => rw [hf, ih]

/-! ### W4. A ratio of powers to `tanh ^ k`: R33, R34, R35, R36 -/
example (x : ℝ) : Real.sinh x ^ 3 * 5 / (5 * Real.cosh x ^ 3) = Real.tanh x ^ 3 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  have hc := Real.cosh_pos x
  field_simp

end H096Guide

/- Guide for M163 (Einstein solids in thermal contact).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (multisets of `Bool`, swapped
products, parity classes).
Assumed: Lean basics.
-/
import Mathlib

namespace M163Guide

/-! # Part R · Reference entries -/

/-! ## Counting through an equivalence -/

/-! ### R1. `Nat.card_congr` · `e : α ≃ β → Nat.card α = Nat.card β` · goal: `Nat.card β` → `Nat.card α`
`α ≃ β` is a bijection packaged with its inverse. `rw [← Nat.card_congr e]` replaces the type on the
right of `e` by the one on the left. -/
example {α β : Type} (e : α ≃ β) (P : ℕ → Prop) (h : P (Nat.card α)) : P (Nat.card β) := by
  rw [← Nat.card_congr e]
  exact h

/-! ### R2. `Sym.equivNatSumOfFintype α n` · `Sym α n ≃ {P : α → ℕ // ∑ i, P i = n}` · goal (inside R1)
A multiset of size `n` over `α` is the same as a multiplicity function `α → ℕ` with total `n`. -/
example {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (P : ℕ → Prop) (h : P (Nat.card (Sym α n))) :
    P (Nat.card {f : α → ℕ // ∑ i, f i = n}) := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype α n)]
  exact h

/-! ### R3. `Nat.card_eq_fintype_card` · `Nat.card α = Fintype.card α` · goal -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α)) : P (Nat.card α) := by
  rw [Nat.card_eq_fintype_card]
  exact h

/-! ### R4. `Sym.card_sym_eq_choose` · `Fintype.card (Sym α k) = (Fintype.card α + k - 1).choose k` · goal
Stars and bars. -/
example {α : Type} [Fintype α] [DecidableEq α] (k : ℕ) (P : ℕ → Prop)
    (h : P ((Fintype.card α + k - 1).choose k)) : P (Fintype.card (Sym α k)) := by
  rw [Sym.card_sym_eq_choose]
  exact h

/-! ### R5. `Fintype.card_fin` · `Fintype.card (Fin n) = n` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Fintype.card (Fin n)) := by
  rw [Fintype.card_fin]
  exact h

/-! ## Subtypes as Finsets -/

/-! ### R6. `Nat.card_eq_finsetCard` · `Nat.card ↥s = s.card`; right to left: `rw [← Nat.card_eq_finsetCard]`
`↥s` is the Finset `s` used as a type: its elements are pairs `⟨x, hx⟩` with `hx : x ∈ s`. -/
example {α : Type} (s : Finset α) (P : ℕ → Prop) (h : P (Nat.card ↥s)) : P s.card := by
  rw [← Nat.card_eq_finsetCard]
  exact h

/-! ### R7. `Finset.Nat.mem_antidiagonalTuple` · `x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n` · goal -/
example (k n : ℕ) (x : Fin k → ℕ) (h : ∑ i, x i = n) : x ∈ Finset.Nat.antidiagonalTuple k n := by
  rw [Finset.Nat.mem_antidiagonalTuple]
  exact h

/-! ### R8. `Equiv.subtypeEquivRight` · `(∀ x, p x ↔ q x) → {x // p x} ≃ {x // q x}` · closes, with R1
`(h x).symm` flips an `↔`. -/
example {α : Type} (p q : α → Prop) (h : ∀ x, q x ↔ p x) :
    Nat.card {x // p x} = Nat.card {x // q x} := by
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (h x).symm)

/-! ## A bijection between two Finsets -/

/-! ### R9. `Finset.card_product` · `(s ×ˢ t).card = s.card * t.card`; right to left: `rw [← Finset.card_product]` -/
example {α β : Type} (s : Finset α) (t : Finset β) (P : ℕ → Prop) (h : P (s ×ˢ t).card) :
    P (s.card * t.card) := by
  rw [← Finset.card_product]
  exact h

/-! ### R10. `Finset.card_nbij' i j` · goal `s.card = t.card` → four goals
`i` goes `s → t`, `j` goes back; the four goals say both land in the right set and undo each other. -/
example {α β : Type} (s : Finset α) (t : Finset β) (i : α → β) (j : β → α)
    (hi : Set.MapsTo i ↑s ↑t) (hj : Set.MapsTo j ↑t ↑s)
    (hl : Set.LeftInvOn j i ↑s) (hr : Set.RightInvOn j i ↑t) : s.card = t.card := by
  refine Finset.card_nbij' i j ?_ ?_ ?_ ?_
  exacts [hi, hj, hl, hr]

/-! ### R11. `intro x hx` on `Set.MapsTo f ↑s ↑t` · context gains `x`, `hx : x ∈ ↑s`; goal `f x ∈ ↑t`
`Set.MapsTo f A B` is defined as `∀ ⦃x⦄, x ∈ A → f x ∈ B`. -/
example {α β : Type} (f : α → β) (s : Finset α) (t : Finset β) (h : ∀ x ∈ s, f x ∈ t) :
    Set.MapsTo f ↑s ↑t := by
  intro x hx
  exact h x hx

/-! ### R12. `Finset.coe_filter`, `Set.mem_setOf_eq` · context: `x ∈ ↑{x ∈ s | p x}` → `x ∈ s ∧ p x` -/
example {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (x : α)
    (hx : x ∈ (↑({y ∈ s | p y}) : Set α)) : p x := by
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
  exact hx.2

/-! ### R13. `Finset.mem_coe` · `a ∈ ↑s ↔ a ∈ s` · goal -/
example {α : Type} (s : Finset α) (a : α) (h : a ∈ s) : a ∈ (↑s : Set α) := by
  simp only [Finset.mem_coe]
  exact h

/-! ### R14. `Finset.coe_product`, `Set.mem_prod`, then R13 · goal: `p ∈ ↑(s ×ˢ t)` → `p.1 ∈ s ∧ p.2 ∈ t` -/
example {α β : Type} (s : Finset α) (t : Finset β) (p : α × β) (h : p.1 ∈ s ∧ p.2 ∈ t) :
    p ∈ (↑(s ×ˢ t) : Set (α × β)) := by
  simp only [Finset.coe_product]
  simp only [Set.mem_prod]
  simp only [Finset.mem_coe]
  exact h

/-! ## Splitting `Fin (a + b)` into two blocks -/

/-! ### R15. `Fin.sum_univ_add` · goal: a sum over `Fin (a + b)` → the first `a` terms + the last `b` terms
`Fin.castAdd b i` is `i : Fin a` seen in `Fin (a + b)`; `Fin.natAdd a j` is `a + j` for `j : Fin b`. -/
example {M : Type} [AddCommMonoid M] (a b : ℕ) (f : Fin (a + b) → M) (P : M → Prop)
    (h : P (∑ i, f (Fin.castAdd b i) + ∑ j, f (Fin.natAdd a j))) : P (∑ i, f i) := by
  rw [Fin.sum_univ_add]
  exact h

/-! ### R16. `Fin.append_left`, `Fin.append_right` · goal: `Fin.append u v` on a block → `u` or `v`
`Fin.append u v : Fin (m + n) → α` is `u` on the first `m` indices and `v` on the last `n`. -/
example {α : Type} (m n : ℕ) (u : Fin m → α) (v : Fin n → α) (i : Fin m) (j : Fin n)
    (P : α → α → Prop) (h : P (u i) (v j)) :
    P (Fin.append u v (Fin.castAdd n i)) (Fin.append u v (Fin.natAdd m j)) := by
  simp only [Fin.append_left, Fin.append_right]
  exact h

/-! ### R17. `omega` · closes linear arithmetic over `ℕ`; a sum `∑ i, f i` counts as one unknown
`omega` knows truncated subtraction: `q - k` with `k ≤ q`. -/
example (n m q k : ℕ) (f : Fin n → ℕ) (g : Fin m → ℕ) (h : ∑ i, f i + ∑ j, g j = q ∧ ∑ i, f i = k) :
    ∑ i, f i = k ∧ ∑ j, g j = q - k := by
  omega

/-! ### R18. `intro x _` on `Set.LeftInvOn j i ↑s` · goal: `j (i x) = x`
`Set.LeftInvOn j i A` is `∀ ⦃x⦄, x ∈ A → j (i x) = x`; `Set.RightInvOn j i B` is the same with `i (j y) = y`. -/
example {α β : Type} (s : Finset α) (i : α → β) (j : β → α) (h : ∀ x, j (i x) = x) :
    Set.LeftInvOn j i ↑s := by
  intro x _
  exact h x

/-! ### R19. `Fin.append_castAdd_natAdd` · closes `Fin.append (f on the first block) (f on the second) = f` -/
example {α : Type} (m n : ℕ) (f : Fin (m + n) → α) :
    Fin.append (fun i => f (Fin.castAdd n i)) (fun j => f (Fin.natAdd m j)) = f := by
  exact Fin.append_castAdd_natAdd

/-! ### R20. `Prod.ext` · goal `x = y` for pairs → `x.1 = y.1` and `x.2 = y.2` -/
example {α β : Type} (x y : α × β) (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  refine Prod.ext ?_ ?_
  exacts [h1, h2]

/-! ### R21. `funext h` · term: from `h : ∀ x, f x = g x` it proves `f = g` (closes the goal) -/
example {α β : Type} (f g : α → β) (h : ∀ x, f x = g x) : f = g := by
  exact funext h

/-! ## Summing over fibres -/

/-! ### R22. `simp only [h]` with `h : ∀ k, f k = g k` · goal: rewrites under `∑ k ∈ s, …`
`rw [h]` fails here: the `k` inside the sum is bound, and `rw` does not rewrite under binders. -/
example (f g : ℕ → ℕ) (h : ∀ k, f k = g k) (s : Finset ℕ) (P : ℕ → Prop)
    (hP : P (∑ k ∈ s, g k)) : P (∑ k ∈ s, f k) := by
  simp only [h]
  exact hP

/-! ### R23. `Finset.card_eq_sum_card_fiberwise` · `MapsTo f s t → s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card`
Goal rewritten, plus the side goal `Set.MapsTo f ↑s ↑t`. Name `f` and `t`: Lean cannot guess them from `s.card`. -/
example {ι M : Type} [DecidableEq M] (f : ι → M) (s : Finset ι) (t : Finset M) (P : ℕ → Prop)
    (h : P (∑ b ∈ t, {a ∈ s | f a = b}.card)) (hf : Set.MapsTo f ↑s ↑t) : P s.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := t)]
  exact h
  exact hf

/-! ### R24. `Finset.sum_congr rfl` · goal `∑ x ∈ s, f x = ∑ x ∈ s, g x` → `∀ x ∈ s, f x = g x` -/
example {ι : Type} (s : Finset ι) (f g : ι → ℕ) (h : ∀ x ∈ s, f x = g x) :
    ∑ x ∈ s, f x = ∑ x ∈ s, g x := by
  refine Finset.sum_congr rfl ?_
  exact h

/-! ### R25. `Finset.mem_range` · `m ∈ Finset.range n ↔ m < n` (`range n = {0, …, n - 1}`) · context -/
example (m n : ℕ) (hm : m ∈ Finset.range (n + 1)) : m < n + 1 := by
  rw [Finset.mem_range] at hm
  exact hm

/-! ### R26. `Nat.lt_succ_iff` · `m < n.succ ↔ m ≤ n` (`n.succ` is `n + 1`); `.mp` uses it left to right -/
example (m n : ℕ) (hm : m < n + 1) : m ≤ n := by
  exact Nat.lt_succ_iff.mp hm

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Multisets of size 3 over `Bool`: R3 → R4, then the size of `Bool` -/
example : Nat.card (Sym Bool 3) = 4 := by
  rw [Nat.card_eq_fintype_card]
  rw [Sym.card_sym_eq_choose]
  rw [Fintype.card_bool]
  rfl

/-! ### W2. A bijection by R10: swapping the factors of a product, with R11, R14, R18 in each goal -/
example {α β : Type} (s : Finset α) (t : Finset β) : (s ×ˢ t).card = (t ×ˢ s).card := by
  refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro p _
    rfl
  · intro p _
    rfl

/-! ### W3. A sum over an appended tuple: R15, then R16 -/
example (m n : ℕ) (u : Fin m → ℕ) (v : Fin n → ℕ) :
    ∑ i, Fin.append u v i = ∑ i, u i + ∑ j, v j := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-! ### W4. Splitting `{0, …, 5}` into parity classes: R23, its side goal by R11, R13, R25, R17 -/
example : (Finset.range 6).card = ∑ r ∈ Finset.range 2, {x ∈ Finset.range 6 | x % 2 = r}.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x % 2) (t := Finset.range 2)]
  intro x _
  simp only [Finset.mem_coe, Finset.mem_range]
  omega

end M163Guide

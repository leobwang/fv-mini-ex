/- Guide for M159 (Density of states of N two-level systems).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (flipping one spin, sums by parity).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Real

namespace M159Guide

/-! # Part R · Reference entries -/

/-! ## Counting subsets: `powersetCard` -/

/-! ### R1. `Finset.card_powersetCard` · goal: `(powersetCard n s).card` → `s.card.choose n`
`Finset.powersetCard n s` is the finset of all `n`-element subsets of `s`; `k.choose n` is `C(k, n)`. -/
example {α : Type} (s : Finset α) (n : ℕ) (P : ℕ → Prop) (h : P (s.card.choose n)) :
    P (Finset.powersetCard n s).card := by
  rw [Finset.card_powersetCard]
  exact h

/-! ### R2. `Finset.card_univ` · goal: `univ.card` → `Fintype.card α`
`Finset.univ : Finset α` is the finset of every element of a finite type `α`. -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α)) :
    P (Finset.univ : Finset α).card := by
  rw [Finset.card_univ]
  exact h

/-! ### R3. `Fintype.card_fin` · goal: `Fintype.card (Fin n)` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Fintype.card (Fin n)) := by
  rw [Fintype.card_fin]
  exact h

/-! ## Counting by a bijection -/

/-! ### R4. `refine Finset.card_nbij' i j ?_ ?_ ?_ ?_` · goal `s.card = t.card` → four goals
`i : α → β` and `j : β → α` are maps you choose; the four goals say: `i` maps `s` into `t`, `j` maps
`t` into `s`, `j (i a) = a` on `s`, and `i (j b) = b` on `t`. -/
example {α β : Type} (s : Finset α) (t : Finset β) (i : α → β) (j : β → α)
    (h1 : Set.MapsTo i s t) (h2 : Set.MapsTo j t s) (h3 : Set.LeftInvOn j i s)
    (h4 : Set.RightInvOn j i t) : s.card = t.card := by
  refine Finset.card_nbij' i j ?_ ?_ ?_ ?_
  exacts [h1, h2, h3, h4]

/-! ### R5. `intro x hx` on `Set.MapsTo f A B` · context gains `x`, `hx : x ∈ A`; goal `f x ∈ B`
`Set.MapsTo f A B` is by definition `∀ ⦃x⦄, x ∈ A → f x ∈ B`, so `intro` sees through it. -/
example {α β : Type} (f : α → β) (A : Set α) (B : Set β) (h : ∀ x, x ∈ A → f x ∈ B) :
    Set.MapsTo f A B := by
  intro x hx
  exact h x hx

/-! ## Membership: casts, filters, set-builder -/

/-! ### R6. `Finset.coe_filter` · goal (or, with `at hx`, context): `↑(s.filter p)` (a `Set`) →
`{x | x ∈ s ∧ p x}` -/
example {α : Type} (p : α → Prop) [DecidablePred p] (s : Finset α) (x : α)
    (h : x ∈ {y | y ∈ s ∧ p y}) : x ∈ (↑(s.filter p) : Set α) := by
  rw [Finset.coe_filter]
  exact h

/-! ### R7. `Set.mem_setOf_eq` · goal (or, with `at hx`, context): `x ∈ {y | q y}` → `q x` -/
example {α : Type} (q : α → Prop) (x : α) (h : q x) : x ∈ {y | q y} := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ### R8. `Finset.mem_univ`, `true_and` · context: `x ∈ univ ∧ A` → `A`
`simp` turns `x ∈ univ` into `True` and `True ∧ A` into `A`. -/
example {α : Type} [Fintype α] (x : α) (A G : Prop) (hx : x ∈ Finset.univ ∧ A) (h : A → G) :
    G := by
  simp only [Finset.mem_univ, true_and] at hx
  exact h hx

/-! ### R9. `Finset.mem_coe` · context: `a ∈ ↑s` (as a `Set`) → `a ∈ s` (as a `Finset`) -/
example {α : Type} (s : Finset α) (a : α) (G : Prop) (ha : a ∈ (↑s : Set α)) (h : a ∈ s → G) :
    G := by
  rw [Finset.mem_coe] at ha
  exact h ha

/-! ### R10. `Finset.mem_powersetCard` · context: `s ∈ powersetCard n t` → `s ⊆ t ∧ s.card = n` -/
example {α : Type} (s t : Finset α) (n : ℕ) (G : Prop) (hs : s ∈ Finset.powersetCard n t)
    (h : s ⊆ t ∧ s.card = n → G) : G := by
  rw [Finset.mem_powersetCard] at hs
  exact h hs

/-! ### R11. `Finset.subset_univ` · goal: `s ⊆ univ` is always true, `simp` erases it -/
example {α : Type} [Fintype α] (s : Finset α) (A : Prop) (h : A) : s ⊆ Finset.univ ∧ A := by
  simp only [Finset.subset_univ, true_and]
  exact h

/-! ### R12. `simpa [lemmas] using e` · closes the goal: simplifies `e`'s type and the goal the same
way, then closes the goal with `e`. -/
example {α : Type} [Fintype α] (s : Finset α) (n : ℕ) (hs : s.card = n) :
    s ∈ Finset.powersetCard n Finset.univ := by
  simpa [Finset.mem_powersetCard] using hs

/-! ### R13. `decide_eq_true_eq` · goal: `decide p = true` → `p`
`decide p : Bool` is the Boolean value of a decidable proposition `p`. -/
example (p : Prop) [Decidable p] (P : Prop → Prop) (h : P p) : P (decide p = true) := by
  rw [decide_eq_true_eq]
  exact h

/-! ### R14. `Finset.filter_mem_eq_of_subset` · `s ⊆ t → t.filter (· ∈ s) = s` · goal -/
example {α : Type} [DecidableEq α] (s t : Finset α) (hst : s ⊆ t) (P : Finset α → Prop) (h : P s) :
    P (t.filter fun x => x ∈ s) := by
  rw [Finset.filter_mem_eq_of_subset hst]
  exact h

/-! ## The two inverse laws -/

/-! ### R15. `intro x hx` on `Set.LeftInvOn g f A` · goal `g (f x) = x`
`Set.LeftInvOn g f A` is `∀ ⦃x⦄, x ∈ A → g (f x) = x`. `Set.RightInvOn g f B` is
`Set.LeftInvOn f g B`, i.e. `∀ ⦃y⦄, y ∈ B → f (g y) = y`: `intro` works the same way. -/
example {α β : Type} (f : α → β) (g : β → α) (A : Set α) (h : ∀ x, x ∈ A → g (f x) = x) :
    Set.LeftInvOn g f A := by
  intro x hx
  exact h x hx

/-! ### R16. `funext i` · goal `F = G` between functions → `F i = G i` -/
example {α β : Type} (F G : α → β) (h : ∀ i, F i = G i) : F = G := by
  funext i
  exact h i

/-! ### R17. `Finset.mem_filter` · goal: `a ∈ s.filter p` → `a ∈ s ∧ p a` -/
example {α : Type} (p : α → Prop) [DecidablePred p] (s : Finset α) (a : α) (h : a ∈ s ∧ p a) :
    a ∈ s.filter p := by
  rw [Finset.mem_filter]
  exact h

/-! ### R18. `Bool.decide_eq_true` · goal: `decide (b = true)` → `b` for a `b : Bool` -/
example (b : Bool) (P : Bool → Prop) (h : P b) : P (decide (b = true)) := by
  rw [Bool.decide_eq_true]
  exact h

/-! ### R19. `ext i` on finsets (lemma `Finset.ext`) · goal `s = t` → `i ∈ s ↔ i ∈ t` -/
example {α : Type} (s t : Finset α) (h : ∀ i, i ∈ s ↔ i ∈ t) : s = t := by
  ext i
  exact h i

/-! ## Regrouping a sum -/

/-! ### R20. `rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := t)]` · goal: `∑ x ∈ s, f x` → a
double sum over the fibres of `g`, plus a side goal `∀ x ∈ s, g x ∈ t`.
`∑ x ∈ s with g x = y, f x` is the sum over `s.filter (g · = y)`, the fibre of `g` over `y`. -/
example {ι κ : Type} [DecidableEq κ] (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → ℝ)
    (P : ℝ → Prop) (h : P (∑ y ∈ t, ∑ x ∈ s with g x = y, f x)) (hg : ∀ x ∈ s, g x ∈ t) :
    P (∑ x ∈ s, f x) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := t)]
  exact h
  exact hg

/-! ### R21. `refine Finset.sum_congr rfl fun y _ => ?_` · goal: equal sums over the same `t` →
the summands at one `y ∈ t` -/
example {κ : Type} (t : Finset κ) (u v : κ → ℝ) (h : ∀ y ∈ t, u y = v y) :
    ∑ y ∈ t, u y = ∑ y ∈ t, v y := by
  refine Finset.sum_congr rfl fun y hy => ?_
  exact h y hy

/-! ### R22. `rw [Finset.sum_congr rfl (g := fun _ => c)]` · goal: the summand → the constant `c`,
plus a side goal `∀ x ∈ s, f x = c` -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (c : ℝ) (P : ℝ → Prop) (h : P (∑ _x ∈ s, c))
    (hf : ∀ x ∈ s, f x = c) : P (∑ x ∈ s, f x) := by
  rw [Finset.sum_congr rfl (g := fun _ => c)]
  exact h
  exact hf

/-! ### R23. `Finset.sum_const` · goal: `∑ _x ∈ s, c` → `s.card • c` (`n • c` is `c + … + c`, n times) -/
example {ι : Type} (s : Finset ι) (c : ℝ) (P : ℝ → Prop) (h : P (s.card • c)) :
    P (∑ _x ∈ s, c) := by
  rw [Finset.sum_const]
  exact h

/-! ### R24. `nsmul_eq_mul` · goal: `n • a` → `↑n * a` (`↑n` is the natural `n` cast to `ℝ`) -/
example (n : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (↑n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ## The side goal `g x ∈ range (N + 1)` -/

/-! ### R25. `Finset.mem_range` · goal: `k ∈ range n` → `k < n` (`range n = {0, …, n - 1}`) -/
example (k n : ℕ) (h : k < n) : k ∈ Finset.range n := by
  rw [Finset.mem_range]
  exact h

/-! ### R26. `Nat.lt_succ_iff` · goal: `k < n + 1` → `k ≤ n` -/
example (k n : ℕ) (h : k ≤ n) : k < n + 1 := by
  rw [Nat.lt_succ_iff]
  exact h

/-! ### R27. `Finset.card_le_univ` · `s.card ≤ Fintype.card α` for any `s : Finset α` -/
example {α : Type} [Fintype α] (s : Finset α) : s.card ≤ Fintype.card α :=
  Finset.card_le_univ s

/-! ### R28. `refine hab.trans ?_` (`le_trans`) · goal `a ≤ c` → `b ≤ c`, given `hab : a ≤ b` -/
example (a b c : ℕ) (hab : a ≤ b) (h : b ≤ c) : a ≤ c := by
  refine hab.trans ?_
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A bijection by `Finset.card_nbij'`: flipping every spin swaps "site 0 up" and "site 0 down"
R4; each `MapsTo`: R5, R6–R8 at the hypothesis, then `simp`; each inverse law: R15, R16, then `simp`. -/
example (n : ℕ) :
    (Finset.univ.filter fun σ : Fin (n + 1) → Bool => σ 0 = true).card =
      (Finset.univ.filter fun σ : Fin (n + 1) → Bool => σ 0 = false).card := by
  refine Finset.card_nbij' (fun σ i => !σ i) (fun σ i => !σ i) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ
    simp [hσ]
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ
    simp [hσ]
  · intro σ _
    funext i
    simp
  · intro σ _
    funext i
    simp

/-! ### W2. Regrouping a sum by parity: R20, R21, R22, R23, R24, R25 -/
example (c : ℕ → ℝ) :
    ∑ x ∈ Finset.range 4, c (x % 2) =
      ∑ r ∈ Finset.range 2, ((Finset.range 4).filter (· % 2 = r)).card * c r := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := (· % 2)) (t := Finset.range 2)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => c r)]
    · rw [Finset.sum_const, nsmul_eq_mul]
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [hx.2]
  · intro x _
    rw [Finset.mem_range]
    exact Nat.mod_lt x (by norm_num)

end M159Guide

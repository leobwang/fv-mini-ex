/- Guide for H037 (Lagrange's theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (right translations, `Fin 6`,
products of three elements).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Finset

namespace H037Guide

/-! # Part R · Reference entries -/

/-! ## Equal finsets, membership in `filter`, `univ`, `image` -/

/-! ### R1. `ext x` (lemma `Finset.ext`) · goal `s = t` → context gains `x`, goal `x ∈ s ↔ x ∈ t` -/
example {α : Type} (s t : Finset α) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

/-! ### R2. `Finset.mem_filter` · `a ∈ filter p s ↔ a ∈ s ∧ p a` · goal -/
example {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (a : α) (P : Prop → Prop)
    (h : P (a ∈ s ∧ p a)) : P (a ∈ s.filter p) := by
  rw [Finset.mem_filter]
  exact h

/-! ### R3. `Finset.mem_univ`, `true_and` · `a ∈ univ` → `True`, then `True ∧ q` → `q` · goal -/
example {α : Type} [Fintype α] (p : α → Prop) (a : α) (P : Prop → Prop) (h : P (p a)) :
    P (a ∈ (univ : Finset α) ∧ p a) := by
  simp only [Finset.mem_univ]
  simp only [true_and]
  exact h

/-! ### R4. `Finset.mem_image` · `b ∈ image f s ↔ ∃ a ∈ s, f a = b` · goal -/
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (b : β) (P : Prop → Prop)
    (h : P (∃ a ∈ s, f a = b)) : P (b ∈ s.image f) := by
  rw [Finset.mem_image]
  exact h

/-! ## Two directions, witnesses, group algebra -/

/-! ### R5. `constructor` on `↔` · goal list: `A ↔ B` → `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exact hab
  exact hba

/-! ### R6. `refine ⟨w, hw, ?_⟩` · goal `∃ a ∈ s, q a` → `q w`
`∃ a ∈ s, q a` is `∃ a, a ∈ s ∧ q a`, so the anonymous constructor takes three parts. -/
example {α : Type} (s : Finset α) (q : α → Prop) (w : α) (hw : w ∈ s) (hq : q w) :
    ∃ a ∈ s, q a := by
  refine ⟨w, hw, ?_⟩
  exact hq

/-! ### R7. `group` · closes an identity that holds in every group (`*`, `⁻¹`, `1`, powers) -/
example {G : Type} [Group G] (a b : G) : (a * b)⁻¹ * a = b⁻¹ := by
  group

/-! ### R8. `rintro ⟨y, hy, rfl⟩` · goal `(∃ a ∈ s, f a = b) → Q b` → context gains `y`, `hy`;
`rfl` substitutes `b := f y` everywhere, so `b` disappears. -/
example {α β : Type} (s : Finset α) (f : α → β) (b : β) (Q : β → Prop) (h : ∀ y ∈ s, Q (f y)) :
    (∃ a ∈ s, f a = b) → Q b := by
  rintro ⟨y, hy, rfl⟩
  exact h y hy

/-! ### R9. `simpa using h` · closes the goal: simplifies `h` and the goal with `simp`, then matches them -/
example {G : Type} [Group G] (H : Subgroup G) (a y : G) (h : y * a * a⁻¹ ∈ H) : y ∈ H := by
  simpa using h

/-! ## Counting an image -/

/-! ### R10. `Finset.card_image_of_injective` · `Injective f → #(image f s) = #s` · goal -/
example {α β : Type} [DecidableEq β] (s : Finset α) (f : α → β) (hf : Function.Injective f)
    (P : ℕ → Prop) (h : P #s) : P #(s.image f) := by
  rw [Finset.card_image_of_injective s hf]
  exact h

/-! ### R11. `mul_right_injective` · `Function.Injective (fun x => a * x)`: left multiplication is injective -/
example {G : Type} [Group G] (a : G) : Function.Injective (fun x => a * x) := by
  exact mul_right_injective a

/-! ## Subgroup membership -/

/-! ### R12. `inv_mul_cancel`, then `Subgroup.one_mem` · goal `a⁻¹ * a ∈ H` → `1 ∈ H` → closed -/
example {G : Type} [Group G] (H : Subgroup G) (a : G) : a⁻¹ * a ∈ H := by
  rw [inv_mul_cancel]
  exact H.one_mem

/-! ### R13. `rw [h] at hx` · context: rewrites the hypothesis `hx`, not the goal -/
example {α : Type} (a b : α) (Q : α → Prop) (h : a = b) (hx : Q a) : Q b := by
  rw [h] at hx
  exact hx

/-! ### R14. `Subgroup.mul_mem` · `x ∈ H → y ∈ H → x * y ∈ H` · context gains the product -/
example {G : Type} [Group G] (H : Subgroup G) (x y : G) (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H := by
  have hxy := H.mul_mem hx hy
  exact hxy

/-! ### R15. `Subgroup.inv_mem` · `x ∈ H → x⁻¹ ∈ H` · context gains the inverse -/
example {G : Type} [Group G] (H : Subgroup G) (x : G) (hx : x ∈ H) : x⁻¹ ∈ H := by
  have hi := H.inv_mem hx
  exact hi

/-! ### R16. `mul_assoc` · `a * b * c = a * (b * c)` · goal (`simp [mul_assoc]` regroups to the right) -/
example {G : Type} [Group G] (a b c : G) (P : G → Prop) (h : P (a * (b * c))) : P (a * b * c) := by
  rw [mul_assoc]
  exact h

/-! ### R17. `mul_inv_cancel_left` · `a * (a⁻¹ * b) = b` · goal (`simp` applies it by itself) -/
example {G : Type} [Group G] (a b : G) (P : G → Prop) (h : P b) : P (a * (a⁻¹ * b)) := by
  rw [mul_inv_cancel_left]
  exact h

/-! ## Counting by fibers -/

/-! ### R18. `Finset.card_univ` · `#univ = Fintype.card α`; right to left: `rw [← Finset.card_univ]` -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P #(univ : Finset α)) :
    P (Fintype.card α) := by
  rw [← Finset.card_univ]
  exact h

/-! ### R19. `Finset.card_eq_sum_card_image f s` · `#s = ∑ b ∈ image f s, #{a ∈ s | f a = b}` · goal
Group the elements of `s` by their value under `f`: each fiber is counted once. -/
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (P : ℕ → Prop)
    (h : P (∑ b ∈ s.image f, #(s.filter (fun a => f a = b)))) : P #s := by
  rw [Finset.card_eq_sum_card_image f s]
  exact h

/-! ### R20. `obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc` · context: `c ∈ image f s` → `a`, and
`c` replaced by `f a`. `-` throws away the part `a ∈ s`. `.mp` is the `→` direction of an `↔`. -/
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (c : β) (hc : c ∈ s.image f)
    (Q : β → Prop) (h : ∀ a, Q (f a)) : Q c := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc
  exact h a

/-! ### R21. `congr 1` · goal `#s = #t` → `s = t` (peel one function application off both sides)
`congr` closes the new goal by itself when it is a hypothesis or `rfl`. -/
example {α : Type} (s t : Finset α) (h : ∀ x, x ∈ s ↔ x ∈ t) : #s = #t := by
  congr 1
  ext x
  exact h x

/-! ### R22. `Finset.sum_const_nat` · `(∀ x ∈ s, f x = m) → ∑ x ∈ s, f x = #s * m` · goal -/
example {α : Type} (s : Finset α) (f : α → ℕ) (m : ℕ) (hf : ∀ x ∈ s, f x = m) (P : ℕ → Prop)
    (h : P (#s * m)) : P (∑ x ∈ s, f x) := by
  rw [Finset.sum_const_nat hf]
  exact h

/-! ### R23. `dvd_mul_left a b` · `a ∣ b * a` · closes the goal -/
example (a b : ℕ) : a ∣ b * a := by
  exact dvd_mul_left a b

/-! ## From `Finite` / `Nat.card` to `Fintype` / `Finset` -/

/-! ### R24. `classical` · makes every proposition decidable for the rest of the proof
Goal and context look the same, but `filter` now accepts any predicate. -/
example {α : Type} [Fintype α] (p : α → Prop) : ∃ s : Finset α, ∀ x, x ∈ s ↔ p x := by
  classical
  exact ⟨univ.filter p, by simp⟩

/-! ### R25. `haveI := Fintype.ofFinite α` · context gains an instance `this : Fintype α` -/
example {α : Type} [Finite α] : ∃ s : Finset α, ∀ x, x ∈ s := by
  haveI := Fintype.ofFinite α
  exact ⟨univ, Finset.mem_univ⟩

/-! ### R26. `Nat.card_eq_fintype_card` · `Nat.card α = Fintype.card α` · goal -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α)) : P (Nat.card α) := by
  rw [Nat.card_eq_fintype_card]
  exact h

/-! ### R27. `Fintype.card_subtype` · `Fintype.card {x // p x} = #{x | p x}` · goal -/
example {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] (P : ℕ → Prop)
    (h : P #(univ.filter p)) : P (Fintype.card {x // p x}) := by
  rw [Fintype.card_subtype]
  exact h

/-! ### R28. `Nat.card_zpowers` · `Nat.card ↥(zpowers a) = orderOf a`; right to left: `rw [← …]` -/
example {G : Type} [Group G] (a : G) (P : ℕ → Prop) (h : P (Nat.card (Subgroup.zpowers a))) :
    P (orderOf a) := by
  rw [← Nat.card_zpowers]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A RIGHT translate `x ↦ x * a` of a finset has the same size: R10 with `mul_left_injective` -/
example {G : Type} [Group G] [DecidableEq G] (s : Finset G) (a : G) :
    #(s.image (· * a)) = #s := by
  rw [Finset.card_image_of_injective s (mul_left_injective a)]

/-! ### W2. Counting by fibers on `Fin 6`: R18 → R19 → R22 → R23
`f n = n % 3` has three fibers of size 2, so `2 ∣ 6`. -/
example : 2 ∣ Fintype.card (Fin 6) := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image (fun n : Fin 6 => n.val % 3) univ]
  have hfib : ∀ c ∈ univ.image (fun n : Fin 6 => n.val % 3),
      #(univ.filter (fun n : Fin 6 => n.val % 3 = c)) = 2 := by
    decide
  rw [Finset.sum_const_nat hfib]
  exact dvd_mul_left _ _

/-! ### W3. From `Finite` and `Nat.card` to a `Finset` count: R24 → R25 → R26 → R27 -/
example {α : Type} [Finite α] (p : α → Prop) : Nat.card {x // p x} ≤ Nat.card α := by
  classical
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.card_le_univ _

/-! ### W4. Closure under `*` and `⁻¹`, then regrouping: R14, R15 inside `simpa [mul_assoc]` (R16, R17) -/
example {G : Type} [Group G] (H : Subgroup G) (a b c : G) (ha : a * b ∈ H) (hc : c * b ∈ H) :
    a * c⁻¹ ∈ H := by
  have h := H.mul_mem ha (H.inv_mem hc)
  simpa [mul_assoc] using h

end H037Guide

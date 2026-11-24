/- Guide for M063 (Finiteness arguments in algebra).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or a goal you do not care about); a hypothesis `h` in an entry
is only there to finish the example and shows what the goal or context became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

namespace M063Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 tools: injective → surjective on a finite type -/

/-! ### R1. `Function.Injective f` · unfold with `intro x y hxy` · context gains `x y hxy`, goal `x = y`
`Function.Injective f` is by definition `∀ x y, f x = f y → x = y`, so `intro` (or a `fun x y hxy => …`
term) opens it directly. -/
example {α β : Type} (f : α → β) (h : ∀ x y, f x = f y → x = y) : Function.Injective f := by
  intro x y hxy
  exact h x y hxy

/-! ### R2. `mul_left_cancel₀` · `a ≠ 0 → a * b = a * c → b = c` · goal `b = c` → `a * b = a * c` -/
example {R : Type} [CommRing R] [IsDomain R] (a b c : R) (ha : a ≠ 0) (h : a * b = a * c) :
    b = c := by
  apply mul_left_cancel₀ ha
  exact h

/-! ### R3. `Finite.injective_iff_surjective` · `[Finite α] → (Injective f ↔ Surjective f)` for `f : α → α`
`.mp` turns a proof of the left side into one of the right side · context gains `hs` -/
example {α : Type} [Finite α] (f : α → α) (hinj : Function.Injective f) (P : Prop)
    (h : Function.Surjective f → P) : P := by
  have hs := Finite.injective_iff_surjective.mp hinj
  exact h hs

/-! ### R4. `obtain ⟨x, hx⟩ := hs y` · `Function.Surjective f` is `∀ y, ∃ x, f x = y`
Apply `hs` to a point and take the existential apart · context gains `x hx` -/
example {α β : Type} (f : α → β) (hs : Function.Surjective f) (y : β) (P : Prop)
    (h : ∀ x, f x = y → P) : P := by
  obtain ⟨x, hx⟩ := hs y
  exact h x hx

/-! ### R5. `exact ⟨w, hw⟩` · closes `∃ y, Q y` when `hw : Q w`, even if `hw` still shows a `fun`
`(fun x => g x) w` and `g w` are the same term after β-reduction; `exact` accepts either. -/
example {α β : Type} [Add β] (g : α → β) (c : β) (w : α) (hw : (fun x => g x + g x) w = c) :
    ∃ y, g y + g y = c := by
  exact ⟨w, hw⟩

/-! ## Part 2 tools: counting elements of a group -/

/-! ### R6. `Nat.Prime.one_lt` · `p.Prime → 1 < p` · context gains `h1 : 1 < p` -/
example (p : ℕ) (hp : p.Prime) (P : Prop) (h : 1 < p → P) : P := by
  have h1 := hp.one_lt
  exact h h1

/-! ### R7. `h ▸ e` · with `h : a = b`, rewrite the type of `e` so that it fits the expected type
Closes `⊢ Q a` from `e : Q b` (the same as `rw [h]; exact e`). -/
example (Q : ℕ → Prop) (a b : ℕ) (h : a = b) (e : Q b) : Q a := by
  exact h ▸ e

/-! ### R8. `Finite.one_lt_card_iff_nontrivial` · `1 < Nat.card α ↔ Nontrivial α`
`haveI : Nontrivial α := …` adds the instance to the context (as `this`), so lemmas that need
`[Nontrivial α]` find it. -/
example {α : Type} [Finite α] (hc : 1 < Nat.card α) (P : Prop) (h : Nontrivial α → P) : P := by
  haveI : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp hc
  exact h this

/-! ### R9. `exists_ne` · `[Nontrivial α] (x : α) : ∃ y, y ≠ x` · with `obtain`, context gains `g hg` -/
example {G : Type} [Group G] [Nontrivial G] (P : Prop) (h : ∀ g : G, g ≠ 1 → P) : P := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact h g hg

/-! ### R10. `Subgroup.zpowers g` · the subgroup `{g ^ k | k : ℤ}` · `Subgroup.mem_zpowers_iff` unfolds it -/
example {G : Type} [Group G] (g x : G) (h : ∃ k : ℤ, g ^ k = x) : x ∈ Subgroup.zpowers g := by
  rw [Subgroup.mem_zpowers_iff]
  exact h

/-! ### R11. `Subgroup.card_subgroup_dvd_card` (Lagrange) · `Nat.card ↥H ∣ Nat.card G` · context gains `hd` -/
example {G : Type} [Group G] (H : Subgroup G) (P : Prop) (h : Nat.card H ∣ Nat.card G → P) : P := by
  have hd := Subgroup.card_subgroup_dvd_card H
  exact h hd

/-! ### R12. `Nat.Prime.eq_one_or_self_of_dvd` · `p.Prime → m ∣ p → m = 1 ∨ m = p` · context gains `h2` -/
example (p m : ℕ) (hp : p.Prime) (hm : m ∣ p) (P : Prop) (h : m = 1 ∨ m = p → P) : P := by
  have h2 := hp.eq_one_or_self_of_dvd m hm
  exact h h2

/-! ### R13. `rcases h with h1 | h1` · `h : A ∨ B` · goal list: one goal with `h1 : A`, one with `h1 : B` -/
example (A B C : Prop) (h : A ∨ B) (ha : A → C) (hb : B → C) : C := by
  rcases h with h1 | h1
  · exact ha h1
  · exact hb h1

/-! ### R14. `Subgroup.card_eq_one` · `Nat.card ↥H = 1 ↔ H = ⊥` · context gains `hb : H = ⊥`
`⊥` is the trivial subgroup `{1}`, `⊤` the whole group. -/
example {G : Type} [Group G] (H : Subgroup G) (h1 : Nat.card H = 1) (P : Prop) (h : H = ⊥ → P) :
    P := by
  have hb := Subgroup.card_eq_one.mp h1
  exact h hb

/-! ### R15. `Subgroup.zpowers_eq_bot` · `zpowers g = ⊥ ↔ g = 1` · goal `zpowers g = ⊥` → `g = 1` -/
example {G : Type} [Group G] (g : G) (h : g = 1) : Subgroup.zpowers g = ⊥ := by
  rw [Subgroup.zpowers_eq_bot]
  exact h

/-! ### R16. `absurd` · `a → ¬a → b` · closes any goal from a fact and its negation
`g ≠ 1` is notation for `¬ (g = 1)`. -/
example {G : Type} [Group G] (g : G) (B : Prop) (h : g = 1) (hn : g ≠ 1) : B := by
  exact absurd h hn

/-! ### R17. `isCyclic_iff_exists_zpowers_eq_top` · `IsCyclic G ↔ ∃ g, zpowers g = ⊤` · goal changes -/
example {G : Type} [Group G] (h : ∃ g : G, Subgroup.zpowers g = ⊤) : IsCyclic G := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact h

/-! ### R18. `Subgroup.eq_top_of_card_eq` · `Nat.card ↥H = Nat.card G → H = ⊤` (needs `[Finite ↥H]`)
· goal `H = ⊤` → `Nat.card ↥H = Nat.card G`. A subgroup of a `Finite` group is found `Finite`
automatically. -/
example {G : Type} [Group G] [Finite G] (H : Subgroup G) (h : Nat.card H = Nat.card G) : H = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  exact h

/-! ### R19. `Eq.trans`, `Eq.symm` · from `h1 : a = b` and `h2 : c = b`, `h1.trans h2.symm : a = c`
`apply Eq.trans h1` changes the goal `a = c` → `b = c`; `h2.symm` closes it. -/
example (a b c : ℕ) (h1 : a = b) (h2 : c = b) : a = c := by
  apply Eq.trans h1
  exact h2.symm

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R3 + R4 + R5 on `f ∘ f`: an injective self-map of a finite type, applied twice, hits `y` -/
example {α : Type} [Finite α] (f : α → α) (hf : Function.Injective f) (y : α) :
    ∃ x, f (f x) = y := by
  have hs := Finite.injective_iff_surjective.mp (hf.comp hf)
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, hx⟩

/-! ### W2. R7 + R11: Lagrange with the group's size given by a hypothesis -/
example {G : Type} [Group G] (H : Subgroup G) (n : ℕ) (hn : Nat.card G = n) : Nat.card H ∣ n := by
  exact hn ▸ Subgroup.card_subgroup_dvd_card H

/-! ### W3. R12 + R13 + R16: a divisor of a prime that is not `1` is the prime -/
example (p m : ℕ) (hp : p.Prime) (hm : m ∣ p) (hne : m ≠ 1) : m = p := by
  rcases hp.eq_one_or_self_of_dvd m hm with h1 | h1
  · exact absurd h1 hne
  · exact h1

end M063Guide

/- Guide for M114 (Polynomial interpolation: existence, and uniqueness by root counting).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (ℕ, ℚ[X] with degree < 3, the nodes 0 and 1).
Assumed: Lean basics.
-/
import Mathlib

open Polynomial

namespace M114Guide

/-! # Part R · Reference entries -/

/-! ## Unique existence and the interpolant -/

/-! ### R1. `refine ⟨w, ⟨?_, ?_⟩, ?_⟩` on `∃!` · goal list: one goal → three
`∃! x, Q x` means `∃ x, Q x ∧ ∀ y, Q y → y = x`. The anonymous constructor takes the witness, the
proof of `Q w` (here itself a pair), and the uniqueness part. -/
example {α : Type} (w : α) (A B : α → Prop) (ha : A w) (hb : B w)
    (h : ∀ y, A y ∧ B y → y = w) : ∃! x, A x ∧ B x := by
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  exact ha
  exact hb
  exact h

/-! ### R2. `Lagrange.interpolate s v r` · the witness: a polynomial in `F[X]`
`Lagrange.interpolate s v` is an `F`-linear map `(ι → F) →ₗ[F] F[X]`; applied to the values `r` it is
the polynomial through the points `(v i, r i)`, `i ∈ s`. The infoview prints the application as
`(Lagrange.interpolate s v) r`. -/
example {F : Type} [Field F] {ι : Type} [DecidableEq ι] (s : Finset ι) (v r : ι → F)
    (Q : F[X] → Prop) (h : Q (Lagrange.interpolate s v r)) : ∃ p : F[X], Q p := by
  refine ⟨Lagrange.interpolate s v r, ?_⟩
  exact h

/-! ### R3. `Lagrange.degree_interpolate_lt` · context gains the degree bound
`(r : ι → F) → Set.InjOn v ↑s → ((Lagrange.interpolate s v) r).degree < ↑s.card` -/
example {F : Type} [Field F] {ι : Type} [DecidableEq ι] (s : Finset ι) (v : ι → F) (r : ι → F)
    (hv : Set.InjOn v s) (G : Prop) (g : ((Lagrange.interpolate s v) r).degree < s.card → G) :
    G := by
  have h := Lagrange.degree_interpolate_lt r hv
  exact g h

/-! ### R4. `Lagrange.eval_interpolate_at_node` · context gains the value at a node
`(r : ι → F) → Set.InjOn v ↑s → i ∈ s → eval (v i) ((Lagrange.interpolate s v) r) = r i` -/
example {F : Type} [Field F] {ι : Type} [DecidableEq ι] (s : Finset ι) (v : ι → F) (r : ι → F)
    (hv : Set.InjOn v s) (i : ι) (hi : i ∈ s) (G : Prop)
    (g : eval (v i) (Lagrange.interpolate s v r) = r i → G) : G := by
  have h := Lagrange.eval_interpolate_at_node r hv hi
  exact g h

/-! ## Uniqueness: reduce to `d = 0` and argue by contradiction -/

/-! ### R5. `rintro y ⟨hA, hB⟩` · context gains `y`, `hA`, `hB`; goal: the conclusion
This is the uniqueness goal R1 leaves, still written with `fun x => …` applied to `y`. -/
example {α : Type} (w : α) (A B : α → Prop) (h : ∀ y, A y → B y → y = w) :
    ∀ y, (fun x => A x ∧ B x) y → y = w := by
  rintro y ⟨hA, hB⟩
  exact h y hA hB

/-! ### R6. `rw [← sub_eq_zero]` · goal `a = b` → `a - b = 0`
`sub_eq_zero : a - b = 0 ↔ a = b`; `←` rewrites the goal from the right side to the left side. -/
example {G : Type} [AddGroup G] (a b : G) (h : a - b = 0) : a = b := by
  rw [← sub_eq_zero]
  exact h

/-! ### R7. `set d := e` · context gains `d : G := e`; every `e` in the goal becomes `d` -/
example {G : Type} [AddGroup G] (a b : G) (P : G → Prop) (h : ∀ x, P x) : P (a - b) := by
  set d := a - b
  exact h d

/-! ### R8. `by_contra hd` · goal `Q` → `False`; context gains `hd : ¬Q` -/
example (Q : Prop) (h : ¬Q → False) : Q := by
  by_contra hd
  exact h hd

/-! ## Degree of a difference -/

/-! ### R9. `Polynomial.degree_sub_le` · context gains `(p - q).degree ≤ max p.degree q.degree` -/
example {R : Type} [Ring R] (p q : R[X]) (G : Prop)
    (g : (p - q).degree ≤ max p.degree q.degree → G) : G := by
  have h := degree_sub_le p q
  exact g h

/-! ### R10. `max_lt` · `b < a → c < a → max b c < a` · goal list: `max b c < a` → two goals -/
example {α : Type} [LinearOrder α] (a b c : α) (hb : b < a) (hc : c < a) : max b c < a := by
  apply max_lt
  exact hb
  exact hc

/-! ### R11. `lt_of_le_of_lt` · `a ≤ b → b < c → a < c` · goal `a < c` → `b < c` -/
example {α : Type} [Preorder α] (a b c : α) (hab : a ≤ b) (hbc : b < c) : a < c := by
  apply lt_of_le_of_lt hab
  exact hbc

/-! ## Root counting -/

/-! ### R12. `apply hd` with `hd : ¬Q` · goal `False` → `Q` -/
example (Q : Prop) (hd : ¬Q) (h : Q) : False := by
  apply hd
  exact h

/-! ### R13. `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` · goal list: `p = 0` → two goals
`(p : R[X]) (t : Finset R) → (∀ x ∈ t, eval x p = 0) → p.natDegree < t.card → p = 0`:
a polynomial with more roots than its degree is zero. -/
example {R : Type} [CommRing R] [IsDomain R] (p : R[X]) (t : Finset R)
    (hroot : ∀ x ∈ t, eval x p = 0) (hcard : p.natDegree < t.card) : p = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p t
  exact hroot
  exact hcard

/-! ### R14. `Finset.mem_image` · `b ∈ Finset.image f s ↔ ∃ a ∈ s, f a = b` · goal: membership → `∃`
On a hypothesis `hx : b ∈ Finset.image f s`, `Finset.mem_image.mp hx : ∃ a ∈ s, f a = b`. -/
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (b : β) (h : ∃ a ∈ s, f a = b) :
    b ∈ s.image f := by
  rw [Finset.mem_image]
  exact h

/-! ### R15. `obtain ⟨a, ha, rfl⟩ := h` · context: `h : ∃ a ∈ s, f a = b` → `a`, `ha`; `b` becomes `f a`
`rfl` as a pattern substitutes the equation `f a = b` everywhere, so `b` disappears. -/
example {α β : Type} (f : α → β) (s : Finset α) (b : β) (h : ∃ a ∈ s, f a = b)
    (P : β → Prop) (hP : ∀ a, P (f a)) : P b := by
  obtain ⟨a, ha, rfl⟩ := h
  exact hP a

/-! ### R16. `simp only [d]` for a `set` variable `d` · goal: `d` → its value -/
example {G : Type} [AddGroup G] (a b : G) (P : G → Prop) (h : ∀ x y, P (x - y)) : P (a - b) := by
  set d := a - b
  simp only [d]
  exact h a b

/-! ### R17. `Polynomial.eval_sub` · `eval x (p - q) = eval x p - eval x q` · goal -/
example {R : Type} [Ring R] (p q : R[X]) (x : R) (P : R → Prop) (h : P (eval x p - eval x q)) :
    P (eval x (p - q)) := by
  rw [eval_sub]
  exact h

/-! ### R18. `sub_self` · `a - a = 0` · goal -/
example {G : Type} [AddGroup G] (a : G) (P : G → Prop) (h : P 0) : P (a - a) := by
  rw [sub_self]
  exact h

/-! ## Counting the nodes -/

/-! ### R19. `Finset.card_image_of_injOn` · `Set.InjOn f ↑s → (Finset.image f s).card = s.card` · goal -/
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (hf : Set.InjOn f s)
    (P : ℕ → Prop) (h : P s.card) : P (s.image f).card := by
  rw [Finset.card_image_of_injOn hf]
  exact h

/-! ### R20. `Polynomial.natDegree_lt_iff_degree_lt` · `p ≠ 0 → (p.natDegree < n ↔ p.degree < ↑n)` · goal -/
example {R : Type} [Semiring R] (p : R[X]) (n : ℕ) (hp : p ≠ 0) (h : p.degree < n) :
    p.natDegree < n := by
  rw [natDegree_lt_iff_degree_lt hp]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `∃!` on `ℕ`: witness, proof, then uniqueness (R1, R5 with `intro`) -/
example : ∃! n : ℕ, n + 2 = 5 := by
  refine ⟨3, rfl, ?_⟩
  intro m hm
  omega

/-! ### W2. Degree of a difference: R11 → R9, then R10 -/
example (p q : ℚ[X]) (hp : p.degree < 3) (hq : q.degree < 3) : (p - q).degree < 3 := by
  apply lt_of_le_of_lt (degree_sub_le p q)
  apply max_lt
  exact hp
  exact hq

/-! ### W3. Root counting on the nodes `{0, 1}` (R13; the roots by `intro` and cases) -/
example (p : ℚ[X]) (hp : p.natDegree < 2) (h0 : eval 0 p = 0) (h1 : eval 1 p = 0) : p = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p {0, 1}
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  · rw [Finset.card_pair (by norm_num)]
    exact hp

end M114Guide

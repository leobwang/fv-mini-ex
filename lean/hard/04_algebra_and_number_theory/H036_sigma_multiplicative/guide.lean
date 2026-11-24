/- Guide for H036 (σ is multiplicative).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (sums `p.1 + p.2`, `range`,
the concrete numbers 4 and 9).
Assumed: Lean basics (E001–E033). New: Mathlib's `Finset`, big sums `∑`, `Nat.divisors`, `∣`, `gcd`,
`Nat.Coprime`, `Set.InjOn`.
-/
import Mathlib

open Finset

namespace H036Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · finset equality as membership -/

/-! ### R1. `ext d` (lemma `Finset.ext`) · goal `s = t` → context gains `d`, goal `d ∈ s ↔ d ∈ t` -/
example {α : Type} (s t : Finset α) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext d
  exact h d

/-! ### R2. `Finset.mem_image` · `b ∈ image f s ↔ ∃ a ∈ s, f a = b` · goal
`∃ a ∈ s, Q a` is notation for `∃ a, a ∈ s ∧ Q a`. -/
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (b : β)
    (h : ∃ a ∈ s, f a = b) : b ∈ image f s := by
  simp only [mem_image]
  exact h

/-! ### R3. `Finset.mem_product` · `p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t` · goal -/
example {α β : Type} (s : Finset α) (t : Finset β) (p : α × β) (h : p.1 ∈ s ∧ p.2 ∈ t) :
    p ∈ s ×ˢ t := by
  simp only [mem_product]
  exact h

/-! ### R4. `Nat.mem_divisors` · `a ∈ n.divisors ↔ a ∣ n ∧ n ≠ 0` · goal -/
example (a n : ℕ) (h : a ∣ n ∧ n ≠ 0) : a ∈ n.divisors := by
  simp only [Nat.mem_divisors]
  exact h

/-! ### R5. `Prod.exists` · `(∃ x : α × β, Q x) ↔ ∃ a b, Q (a, b)` · goal: one pair → two numbers -/
example {α β : Type} (Q : α × β → Prop) (h : ∃ a b, Q (a, b)) : ∃ x : α × β, Q x := by
  simp only [Prod.exists]
  exact h

/-! ### R6. `constructor` on `↔` · goal list: `A ↔ B` → `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exact hab
  exact hba

/-! ### R7. `rintro ⟨h1, h2⟩` · goal `A ∧ B → C` → context gains `h1 : A`, `h2 : B`, goal `C` -/
example (A B C : Prop) (f : A → B → C) : A ∧ B → C := by
  rintro ⟨h1, h2⟩
  exact f h1 h2

/-! ### R8. `rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩` · the pattern `rfl` substitutes the equation away
The hypothesis `f a b = x` is used to replace `x` by `f a b` everywhere. -/
example {α γ : Type} (Q Q' : α → Prop) (f : α → α → γ) (G : γ → Prop) (x : γ)
    (h : ∀ a b, Q a → Q' b → G (f a b)) :
    (∃ a b, (Q a ∧ Q' b) ∧ f a b = x) → G x := by
  rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
  exact h a b ha hb

/-! ### R9. `refine ⟨x, y, ⟨hA, hB⟩, ?_⟩` · goal `∃ a b, (A a ∧ B b) ∧ E a b` → `E x y`
Give the witnesses and the proofs you have now; each `?_` becomes a goal. -/
example (A B : ℕ → Prop) (E : ℕ → ℕ → Prop) (x y : ℕ) (hA : A x) (hB : B y) (hE : E x y) :
    ∃ a b, (A a ∧ B b) ∧ E a b := by
  refine ⟨x, y, ⟨hA, hB⟩, ?_⟩
  exact hE

/-! ### R10. `Nat.gcd_dvd_right` · `a.gcd n ∣ n` · closes the goal
`a.gcd n` is `Nat.gcd a n`; `a ∣ n` ("a divides n") is `∃ c, n = a * c`. -/
example (a n : ℕ) : a.gcd n ∣ n := by
  exact Nat.gcd_dvd_right a n

/-! ### R11. `a ≠ 0` is `a = 0 → False`: `intro ha`, then `simp [ha]` · goal → `False`
In term form: `fun ha => hab (by simp [ha])`. -/
example (a b : ℕ) (hab : a * b ≠ 0) : a ≠ 0 := by
  intro ha
  exact hab (by simp [ha])

/-! ### R12. `Nat.Coprime.gcd_mul` · `m.Coprime n → k.gcd (m * n) = k.gcd m * k.gcd n`
`m.Coprime n` is `Nat.Coprime m n`, which unfolds to `m.gcd n = 1`. Right to left: `rw [← …]`. -/
example (k m n : ℕ) (hc : m.Coprime n) (P : ℕ → Prop) (h : P (k.gcd (m * n))) :
    P (k.gcd m * k.gcd n) := by
  rw [← Nat.Coprime.gcd_mul k hc]
  exact h

/-! ### R13. `Nat.gcd_eq_left` · `a ∣ n → a.gcd n = a` · goal -/
example (a n : ℕ) (hd : a ∣ n) (P : ℕ → Prop) (h : P a) : P (a.gcd n) := by
  rw [Nat.gcd_eq_left hd]
  exact h

/-! ### R14. `mul_dvd_mul` · `a ∣ b → c ∣ d → a * c ∣ b * d` · closes the goal -/
example {α : Type} [CommSemigroup α] (a b c d : α) (h1 : a ∣ b) (h2 : c ∣ d) : a * c ∣ b * d := by
  exact mul_dvd_mul h1 h2

/-! ### R15. `mul_ne_zero` · `a ≠ 0 → b ≠ 0 → a * b ≠ 0` · closes the goal -/
example (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  exact mul_ne_zero ha hb

/-! ## Part 2 · injectivity on a finset -/

/-! ### R16. `rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq heq` on `Set.InjOn f s` · context gains both points
`Set.InjOn f s` unfolds to `∀ ⦃x₁⦄, x₁ ∈ s → ∀ ⦃x₂⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂`; `rintro`
unfolds it, and `⟨a, b⟩` splits a pair into its two components. -/
example {α β γ : Type} (f : α × β → γ) (s : Set (α × β))
    (h : ∀ a b a' b', (a, b) ∈ s → (a', b') ∈ s → f (a, b) = f (a', b') → (a, b) = (a', b')) :
    Set.InjOn f s := by
  rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq heq
  exact h a b a' b' hp hq heq

/-! ### R17. `Finset.coe_product` · `↑(s ×ˢ t) = ↑s ×ˢ ↑t` · context, with `simp only […] at hp`
`↑s : Set α` is the finset `s` viewed as a set. -/
example {α β : Type} (s : Finset α) (t : Finset β) (p : α × β) (hp : p ∈ (↑(s ×ˢ t) : Set (α × β)))
    (h : p ∈ (↑s : Set α) ×ˢ (↑t : Set β) → False) : False := by
  simp only [coe_product] at hp
  exact h hp

/-! ### R18. `Set.mem_prod` · `p ∈ S ×ˢ T ↔ p.1 ∈ S ∧ p.2 ∈ T` (sets) · context -/
example {α β : Type} (S : Set α) (T : Set β) (p : α × β) (hp : p ∈ S ×ˢ T)
    (h : p.1 ∈ S ∧ p.2 ∈ T → False) : False := by
  simp only [Set.mem_prod] at hp
  exact h hp

/-! ### R19. `Finset.mem_coe` · `a ∈ ↑s ↔ a ∈ s` · context: set membership → finset membership -/
example {α : Type} (s : Finset α) (a : α) (hp : a ∈ (↑s : Set α)) (h : a ∈ s → False) :
    False := by
  simp only [mem_coe] at hp
  exact h hp

/-! ### R20. `change T at heq` · context: replace a hypothesis by a definitionally equal form
Here it evaluates the anonymous function `fun p => p.1 + p.2` at the pair `(a, b)`. -/
example (a b c d : ℕ)
    (heq : (fun p : ℕ × ℕ => p.1 + p.2) (a, b) = (fun p : ℕ × ℕ => p.1 + p.2) (c, d))
    (h : a + b = c + d → False) : False := by
  change a + b = c + d at heq
  exact h heq

/-! ### R21. `Nat.Coprime.coprime_dvd_left` · `a ∣ m → m.Coprime n → a.Coprime n` · context
Dot notation: for `hc : m.Coprime n`, `hc.coprime_dvd_left ha` means
`Nat.Coprime.coprime_dvd_left ha hc` (`hc` fills the first argument of type `Nat.Coprime _ _`). -/
example (a m n : ℕ) (hc : m.Coprime n) (ha : a ∣ m) (h : a.Coprime n → False) : False := by
  have h1 : a.Coprime n := hc.coprime_dvd_left ha
  exact h h1

/-! ### R22. `Nat.Coprime.coprime_dvd_right` · `b ∣ n → a.Coprime n → a.Coprime b` · context -/
example (a b n : ℕ) (hc : a.Coprime n) (hb : b ∣ n) (h : a.Coprime b → False) : False := by
  have h1 : a.Coprime b := hc.coprime_dvd_right hb
  exact h h1

/-! ### R23. `Nat.Coprime.dvd_of_dvd_mul_right` · `k.Coprime n → k ∣ m * n → k ∣ m` · context -/
example (k m n : ℕ) (hc : k.Coprime n) (hd : k ∣ m * n) (h : k ∣ m → False) : False := by
  have h1 : k ∣ m := hc.dvd_of_dvd_mul_right hd
  exact h h1

/-! ### R24. `dvd_mul_right` · `a ∣ a * b` · closes the goal -/
example {α : Type} [Semigroup α] (a b : α) : a ∣ a * b := by
  exact dvd_mul_right a b

/-! ### R25. `heq ▸ e` · rewrite the TYPE of the term `e` with `heq : x = y` · context
From `e : P x` it builds a term of type `P y`; the expected type (here given by `have`) tells it which. -/
example {α : Type} (x y : α) (P : α → Prop) (heq : x = y) (e : P x) (h : P y → False) : False := by
  have h1 : P y := heq ▸ e
  exact h h1

/-! ### R26. `Nat.dvd_antisymm` · `a ∣ b → b ∣ a → a = b` · context -/
example (a b : ℕ) (h1 : a ∣ b) (h2 : b ∣ a) (h : a = b → False) : False := by
  have h3 : a = b := Nat.dvd_antisymm h1 h2
  exact h h3

/-! ### R27. `obtain rfl := e` with `e : a = a'` · context: the variable `a'` is replaced by `a` everywhere -/
example (a a' b b' : ℕ) (e : a = a') (heq : a * b = a' * b') (h : a * b = a * b' → False) :
    False := by
  obtain rfl := e
  exact h heq

/-! ### R28. `Nat.pos_of_ne_zero` · `n ≠ 0 → 0 < n` · closes the goal -/
example (n : ℕ) (hn : n ≠ 0) : 0 < n := by
  exact Nat.pos_of_ne_zero hn

/-! ### R29. `Nat.pos_of_dvd_of_pos` · `a ∣ n → 0 < n → 0 < a` · closes the goal -/
example (a n : ℕ) (hd : a ∣ n) (hn : 0 < n) : 0 < a := by
  exact Nat.pos_of_dvd_of_pos hd hn

/-! ### R30. `Nat.eq_of_mul_eq_mul_left` · `0 < a → a * b = a * c → b = c` · closes the goal -/
example (a b c : ℕ) (ha : 0 < a) (heq : a * b = a * c) : b = c := by
  exact Nat.eq_of_mul_eq_mul_left ha heq

/-! ### R31. `Prod.ext` · `p.1 = q.1 → p.2 = q.2 → p = q` · goal: a pair equation → two equations
`(a, b).1` reduces to `a`, so for `(a, b) = (a, c)` the first part is `rfl`. -/
example {α β : Type} (a : α) (b c : β) (hbc : b = c) : (a, b) = (a, c) := by
  exact Prod.ext rfl hbc

/-! ## Part 3 · reindexing and splitting sums -/

/-! ### R32. `Finset.sum_image` · `Set.InjOn g ↑s → ∑ x ∈ image g s, f x = ∑ x ∈ s, f (g x)` · goal
A sum over the image of `s` is a sum over `s` itself, provided `g` hits no value twice on `s`. -/
example {κ ι : Type} [DecidableEq ι] (s : Finset κ) (g : κ → ι) (f : ι → ℕ)
    (hg : Set.InjOn g ↑s) (P : ℕ → Prop) (h : P (∑ x ∈ s, f (g x))) :
    P (∑ x ∈ image g s, f x) := by
  rw [sum_image hg]
  exact h

/-! ### R33. `Finset.sum_mul_sum` · `(∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j` · goal -/
example {ι κ : Type} (s : Finset ι) (t : Finset κ) (f : ι → ℕ) (g : κ → ℕ) (P : ℕ → Prop)
    (h : P (∑ i ∈ s, ∑ j ∈ t, f i * g j)) : P ((∑ i ∈ s, f i) * ∑ j ∈ t, g j) := by
  rw [sum_mul_sum]
  exact h

/-! ### R34. `Finset.sum_product` · `∑ x ∈ s ×ˢ t, f x = ∑ x ∈ s, ∑ y ∈ t, f (x, y)` · goal -/
example {α β : Type} (s : Finset α) (t : Finset β) (f : α × β → ℕ) (P : ℕ → Prop)
    (h : P (∑ x ∈ s, ∑ y ∈ t, f (x, y))) : P (∑ x ∈ s ×ˢ t, f x) := by
  rw [sum_product]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R2–R5 on a SUM image (`p.1 + p.2`, not the exercise's product): what the `simp only` leaves -/
example (k l x : ℕ) (h : ∃ a b, ((a ∣ k ∧ k ≠ 0) ∧ b ∣ l ∧ l ≠ 0) ∧ a + b = x) :
    x ∈ image (fun p : ℕ × ℕ => p.1 + p.2) (k.divisors ×ˢ l.divisors) := by
  simp only [mem_image, mem_product, Nat.mem_divisors, Prod.exists]
  exact h

/-! ### W2. The gcd split (R12, R13) on concrete coprime numbers 4 and 9 -/
example (d : ℕ) (hd : d ∣ 4 * 9) : d.gcd 4 * d.gcd 9 = d := by
  have hc : Nat.Coprime 4 9 := by norm_num
  rw [← Nat.Coprime.gcd_mul d hc]
  rw [Nat.gcd_eq_left hd]

/-! ### W3. The coprime chain (R21 → R22 → R23 with R24, R25), written with `|>.`
`e |>.f x` means `(e).f x`: it continues the dot chain on the result of `e`. -/
example (a b a' b' : ℕ) (ha : a ∣ 4) (hb' : b' ∣ 9) (heq : a * b = a' * b') : a ∣ a' := by
  have hc : Nat.Coprime 4 9 := by norm_num
  exact (hc.coprime_dvd_left ha).coprime_dvd_right hb'
    |>.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a b)

/-! ### W4. Reindexing a sum over an image (R32) without the `InjOn` argument
`rw [sum_image]` then leaves `Set.InjOn …` as a new goal, proved here by hand (R16 with `intro`). -/
example : ∑ x ∈ image (fun k : ℕ => 2 * k) (range 4), x = ∑ k ∈ range 4, 2 * k := by
  rw [sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hxy

/-! ### W5. Product of two sums = a sum over pairs: R33 on the left side, R34 on the right side
After both rewrites the two sides agree up to evaluating `(fun p => …) (i, j)`, and `rw` closes
the goal with `rfl` by itself. -/
example (s t : Finset ℕ) :
    (∑ i ∈ s, (i + 1)) * (∑ j ∈ t, j) = ∑ p ∈ s ×ˢ t, (p.1 + 1) * p.2 := by
  rw [sum_mul_sum]
  rw [sum_product]

end H036Guide

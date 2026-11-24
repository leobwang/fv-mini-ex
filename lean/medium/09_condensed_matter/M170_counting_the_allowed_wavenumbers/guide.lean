/- Guide for M170 (Counting the allowed wavenumbers).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on sets and maps that are NOT the exercise's (no physlib).
Assumed: Lean basics.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace M170Guide

/-! # Part R · Reference entries -/

/-! ## A set described by a formula → the range of a function -/

/-! ### R1. `ext x` (lemma `Set.ext`) · goal `s = t` → context gains `x`, goal `x ∈ s ↔ x ∈ t` -/
example {α : Type} (s t : Set α) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

/-! ### R2. `simp only [TightBindingChain.QuantaWaveNumber]` · goal: the name → its body, a set-builder
`↑↑n` is `n : Fin T.N` cast twice: → `ℕ` → `ℝ`. `↑(T.N / 2)` is the natural number `⌊N/2⌋` cast to `ℝ`. -/
example (T : TightBindingChain) (x : ℝ)
    (h : x ∈ {x | ∃ n : Fin T.N, 2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x}) :
    x ∈ T.QuantaWaveNumber := by
  simp only [TightBindingChain.QuantaWaveNumber]
  exact h

/-! ### R3. `Set.mem_setOf_eq` · `(a ∈ {x | p x}) = p a` · goal: membership in a set-builder → the property -/
example {α : Type} (p : α → Prop) (a : α) (h : p a) : a ∈ {x | p x} := by
  simp only [Set.mem_setOf_eq]
  exact h

/-! ### R4. `Set.mem_range` · `a ∈ Set.range f ↔ ∃ y, f y = a` · goal: membership in a range → an `∃`
If both sides of an `↔` become the same text, `simp only` closes the goal by itself. -/
example {α ι : Type} (f : ι → α) (a : α) (h : ∃ i, f i = a) : a ∈ Set.range f := by
  simp only [Set.mem_range]
  exact h

/-! ## Counting a range -/

/-! ### R5. `Set.ncard_range_of_injective` · `Function.Injective f → (Set.range f).ncard = Nat.card ι`
`rw` with it rewrites the goal AND adds the side goal `Function.Injective f` at the end of the list. -/
example {α ι : Type} (f : ι → α) (n : ℕ) (hf : Function.Injective f) (h : Nat.card ι = n) :
    (Set.range f).ncard = n := by
  rw [Set.ncard_range_of_injective]
  exact h
  exact hf

/-! ### R6. `Nat.card_eq_fintype_card` · `Nat.card α = Fintype.card α` · goal: for a finite type -/
example {α : Type} [Fintype α] (n : ℕ) (h : Fintype.card α = n) : Nat.card α = n := by
  rw [Nat.card_eq_fintype_card]
  exact h

/-! ### R7. `Fintype.card_fin` · `Fintype.card (Fin k) = k` · goal
When the goal becomes `k = k`, `rw` closes it by itself (it tries `rfl` after rewriting). -/
example (k : ℕ) (P : ℕ → Prop) (h : P k) : P (Fintype.card (Fin k)) := by
  rw [Fintype.card_fin]
  exact h

/-! ## Injectivity -/

/-! ### R8. `intro a b h` on `Function.Injective f` · goal `Function.Injective f` → context gains
`a b` and `h : f a = f b`, goal `a = b`. (`Function.Injective f` is by definition
`∀ a b, f a = f b → a = b`; `intro` sees through the name.) -/
example {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) : Function.Injective f := by
  intro a b h
  exact hf a b h

/-! ### R9. `TightBindingChain.a_pos` · `T.a_pos : 0 < T.a` · context gains the positivity of the spacing -/
example (T : TightBindingChain) (G : Prop) (g : 0 < T.a → G) : G := by
  have ha := T.a_pos
  exact g ha

/-! ### R10. `NeZero.pos` · `[NeZero n] → 0 < n` · context gains `0 < n` (in `ℕ`)
A `TightBindingChain` carries an instance `NeZero T.N` (the chain has at least one site). -/
example (n : ℕ) [NeZero n] (G : Prop) (g : 0 < n → G) : G := by
  have hn := NeZero.pos n
  exact g hn

/-! ### R11. `exact_mod_cast e` · closes a goal that is `e`'s statement up to casts `ℕ → ℝ`
Here it uses `Nat.cast_pos : 0 < (↑n : ℝ) ↔ 0 < n`. -/
example (n : ℕ) (hn : 0 < n) : (0 : ℝ) < n := by
  exact_mod_cast hn

/-! ### R12. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` built from `+ * / ^`, numerals, `Real.pi`,
and atoms `x` with a hypothesis `0 < x` in the context -/
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : Real.pi / (x * y) ≠ 0 := by
  positivity

/-! ### R13. `mul_left_cancel₀` · `a ≠ 0 → a * b = a * c → b = c` · context gains the cancelled equation -/
example {α : Type} [MonoidWithZero α] [IsCancelMulZero α] (a b c : α) (ha : a ≠ 0) (h : a * b = a * c) :
    b = c := by
  have h' := mul_left_cancel₀ ha h
  exact h'

/-! ### R14. `sub_left_inj` · `b - a = c - a ↔ b = c` · with `.mp`: context gains the unshifted equation -/
example {α : Type} [AddGroup α] (a b c : α) (h : b - a = c - a) : b = c := by
  have h' := sub_left_inj.mp h
  exact h'

/-! ### R15. `Fin.ext` · `(↑m : ℕ) = ↑n → m = n` · goal: equality in `Fin k` → equality of the values -/
example {k : ℕ} (m n : Fin k) (h : (m : ℕ) = n) : m = n := by
  apply Fin.ext
  exact h

/-! ### R16. `Nat.cast_inj` · `(↑a : ℝ) = ↑b ↔ a = b` · with `.mp`: context gains the equation in `ℕ`
`exact_mod_cast h` (R11) does the same step when it closes the goal. -/
example (a b : ℕ) (h : (a : ℝ) = b) : a = b := by
  have h' := Nat.cast_inj.mp h
  exact h'

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A set-builder written as a range: R1, R3, R4 -/
example : {x : ℝ | ∃ n : Fin 4, 3 * (n : ℝ) + 1 = x} = Set.range (fun n : Fin 4 => 3 * (n : ℝ) + 1) := by
  ext x
  simp only [Set.mem_setOf_eq]
  simp only [Set.mem_range]

/-! ### W2. Injectivity of an affine map on `Fin 4`: R8, then cancel (R13, R14), then cast back (R15, R16)
After `intro`, `h` still shows the `fun`: `(fun n => …) m = (fun n => …) n`. The lemmas see through it. -/
example : Function.Injective (fun n : Fin 4 => 3 * ((n : ℝ) - 2)) := by
  intro m n h
  have h1 := mul_left_cancel₀ (by norm_num : (3 : ℝ) ≠ 0) h
  have h2 := sub_left_inj.mp h1
  apply Fin.ext
  exact_mod_cast h2

/-! ### W3. Counting a range: R5, R6, R7, with the injectivity left as the side goal -/
example (f : Fin 4 → ℝ) (hf : Function.Injective f) : (Set.range f).ncard = 4 := by
  rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact hf

end M170Guide

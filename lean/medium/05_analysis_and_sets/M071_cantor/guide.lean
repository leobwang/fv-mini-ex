/- Guide for M071 (Cantor's theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" and `G` for an arbitrary goal; `k` or `h…` hypotheses in an
entry are only there to finish the example and show what the goal or context became.
Part W: worked combinations on objects that are NOT the exercise's (the liar `P ↔ ¬P`, Nat-valued
diagonals, a concrete set of naturals).
Assumed: Lean basics (E001–E033), in particular `intro`/`exact` (E003), `↔` and `obtain` (E005),
`∃` and `⟨_, _⟩` (E007), `¬` (E008), `by_cases` (E013), `cases` on `Bool` and `simp_all` (E016).
-/
import Mathlib

namespace M071Guide

/-! # Part R · Reference entries -/

/-! ## Using a surjectivity hypothesis -/

/-! ### R1. `intro hg` on `¬ Function.Surjective g` · context gains `hg`, goal becomes `False`
`¬ A` is `A → False`. `Function.Surjective g` is Mathlib's name for
`∀ b, ∃ a, g a = b` ("every `b` is hit"). -/
example {α β : Type} (g : α → β) (k : Function.Surjective g → False) :
    ¬ Function.Surjective g := by
  intro hg
  exact k hg

/-! ### R2. `obtain ⟨a, ha⟩ := hg b` · context gains a witness `a` and `ha : g a = b`
`hg : Function.Surjective g` is a function: give it the `b` you choose and it returns
`∃ a, g a = b`, which `obtain` opens. Choosing `b` well (a diagonal) is the whole idea. -/
example {α β : Type} (g : α → β) (hg : Function.Surjective g) (b : β) (G : Prop)
    (k : ∀ a, g a = b → G) : G := by
  obtain ⟨a, ha⟩ := hg b
  exact k a ha

/-! ## Sets and set-builder notation -/

/-! ### R3. `Set.mem_setOf_eq` · `a ∈ {x | p x} = p a` · goal: membership in a set-builder → the predicate
`Set α` is `α → Prop` (a predicate on `α`), and `{x | p x}` is the set of `x` with `p x`. -/
example {α : Type} (p : α → Prop) (a : α) (P : Prop → Prop) (h : P (p a)) :
    P (a ∈ {x | p x}) := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ### R4. `exact h` up to unfolding · closes `a ∈ {x | p x}` from `h : p a` (and back)
R3 holds by definition (`rfl`), so `exact` accepts either form without any rewriting. -/
example {α : Type} (p : α → Prop) (a : α) (h : p a) : a ∈ {x | p x} := by
  exact h

/-! ### R5. `rw [hs] at h2` · context: `h2` rewritten with `hs : s = t`; goal unchanged
`rw … at h` rewrites a hypothesis instead of the goal. `have h2 := h1` first keeps a copy of `h1`. -/
example {α : Type} (s t : Set α) (a : α) (hs : s = t) (h2 : a ∈ s) : a ∈ t := by
  rw [hs] at h2
  exact h2

/-! ## Working with `↔` and `¬` -/

/-! ### R6. `constructor` on `A ↔ B` · goal list: two implications `A → B` and `B → A` -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exact hab
  exact hba

/-! ### R7. `by_cases hp : A` · goal list: one goal with `hp : A`, one with `hp : ¬A` (excluded middle) -/
example (A G : Prop) (k1 : A → G) (k2 : ¬A → G) : G := by
  by_cases hp : A
  exact k1 hp
  exact k2 hp

/-! ### R8. `Iff.mp`, `Iff.mpr` · `(h : A ↔ B) : A → B` and `B → A`; written `h.mp`, `h.mpr` -/
example (A B : Prop) (h : A ↔ B) (ha : A) (hb : B) : B ∧ A := by
  exact ⟨h.mp ha, h.mpr hb⟩

/-! ### R9. `exact hn ha` · closes `False` from `hn : ¬A` and `ha : A` (a negation is a function to `False`)
`a ∉ s` is `¬ (a ∈ s)`, so it is used the same way. -/
example {α : Type} (s : Set α) (a : α) (hn : a ∉ s) (ha : a ∈ s) : False := by
  exact hn ha

/-! ## A diagonal sequence that differs from every row -/

/-! ### R10. `refine ⟨w, fun n h => ?_⟩` · goal `∃ g, ∀ n, F n ≠ g` → context `n`, `h : F n = w`, goal `False`
`a ≠ b` is notation for `a = b → False`, so a proof of `∀ n, F n ≠ w` is a function of `n` and
`h : F n = w` returning `False`. -/
example {γ : Type} (F : ℕ → γ) (w : γ) (hw : ∀ n, F n = w → False) : ∃ g, ∀ n, F n ≠ g := by
  refine ⟨w, fun n h => ?_⟩
  exact hw n h

/-! ### R11. `congrFun` · `(h : u = v) (x : α) : u x = v x` · context gains the value equation
Equal functions take equal values. If `v` is a `fun`, Lean shows the value β-reduced:
`(fun y => s (u y)) x` appears as `s (u x)`. -/
example {α β : Type} (v u : α → β) (s : β → β) (h : v = fun y => s (u y)) (x : α) (G : Prop)
    (k : v x = s (u x) → G) : G := by
  have := congrFun h x
  exact k this

/-! ### R12. `cases hb : e` · goal list: one goal per value of the Bool term `e`, with `hb` recording it
`e` may be a compound term (`F n n`); hypotheses that mention `e` are NOT rewritten (R13 does that). -/
example (e : Bool) (G : Prop) (h0 : e = false → G) (h1 : e = true → G) : G := by
  cases hb : e
  exact h0 hb
  exact h1 hb

/-! ### R13. `simp_all` · simplifies every hypothesis with the others and the goal with all of them;
closes the goal when a hypothesis becomes `False`. `!b` is Bool negation: `!false = true`.
Here `hb` turns `h` into `false = true`, which is `False`. -/
example (F : ℕ → Bool) (n : ℕ) (h : F n = !F n) (hb : F n = false) : False := by
  simp_all

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The liar: no proposition is equivalent to its own negation (R7, R8, R9) -/
example (Q : Prop) (h : Q ↔ ¬Q) : False := by
  by_cases hq : Q
  · exact h.mp hq hq
  · exact hq (h.mpr hq)

/-! ### W2. Rewrite a hypothesis to a set-builder, then read off the predicate (R5, R4) -/
example (s : Set ℕ) (hs : s = {n | n < 3}) (h1 : 1 ∈ s) : 1 < 3 := by
  rw [hs] at h1
  exact h1

/-! ### W3. A Nat-valued diagonal differs from every row: R10, R11, then `omega` (linear arithmetic) -/
example (F : ℕ → ℕ → ℕ) : ∃ g : ℕ → ℕ, ∀ n, F n ≠ g := by
  refine ⟨fun n => F n n + 1, fun n h => ?_⟩
  have := congrFun h n
  omega

/-! ### W4. Split a Bool term and let `simp_all` finish (R12, R13) -/
example (F : ℕ → Bool) (h : F 0 = !F 0) : False := by
  cases hb : F 0 <;> simp_all

end M071Guide

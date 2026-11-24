/- Guide for E090 (choose).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`α β : Type` are arbitrary types, `Q : α → β → Prop` (or `Q : α → Prop`) is an arbitrary property and
`P : α → Prop` stands for "the rest of the goal". A hypothesis in an entry whose name starts with `h`
is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033), in particular `exact` (E003), anonymous constructors `⟨_, _⟩` for
`∧` and `∃` (E004, E007), `fun` as a proof of `∀` (E004), `unfold` (E012, E030) and `refine` with `?_` (E031).
-/
import Mathlib

namespace E090Guide

/-! # Part R · Reference entries -/

/-! ## From `∀ a, ∃ b, …` to a function -/

/-! ### R1. `choose g hg using h` · context: `h : ∀ a, ∃ b, Q a b` → `g : α → β`, `hg : ∀ a, Q a (g a)`
Mathlib tactic. It picks one witness `g a` for every `a` (a Skolem function) and removes `h`.
The goal `G` is untouched; `k` only finishes the example. -/
example {α β : Type} (Q : α → β → Prop) (G : Prop) (h : ∀ a, ∃ b, Q a b)
    (k : ∀ g : α → β, (∀ a, Q a (g a)) → G) : G := by
  choose g hg using h
  exact k g hg

/-! ### R2. `refine ⟨g, ?_⟩` · goal `∃ f, R f` → `R g`
Give the function as the witness. When `R g` is literally a hypothesis `hg`, `exact ⟨g, hg⟩` does
this step and closes the goal at once. -/
example {α β : Type} (Q : α → β → Prop) (g : α → β) (hg : ∀ a, Q a (g a)) :
    ∃ f : α → β, ∀ a, Q a (f a) := by
  refine ⟨g, ?_⟩
  exact hg

/-! ### R3. `choose g hA hB using h` · context: `∃ b, A a b ∧ B a b` is split into two facts
With more names than one, `choose` also takes the `∧` apart: `hA : ∀ a, A a (g a)` and
`hB : ∀ a, B a (g a)`. The goal `G` is untouched; `k` only finishes the example. -/
example {α β : Type} (A B : α → β → Prop) (G : Prop) (h : ∀ a, ∃ b, A a b ∧ B a b)
    (k : ∀ g : α → β, (∀ a, A a (g a)) → (∀ a, B a (g a)) → G) : G := by
  choose g hA hB using h
  exact k g hA hB

/-! ### R4. `exact fun a => ⟨hA a, hB a⟩` · closes `∀ a, A a (g a) ∧ B a (g a)`
A proof of `∀ a, X a ∧ Y a` is a function that sends each `a` to a pair of proofs. -/
example {α β : Type} (A B : α → β → Prop) (g : α → β) (hA : ∀ a, A a (g a))
    (hB : ∀ a, B a (g a)) : ∀ a, A a (g a) ∧ B a (g a) := by
  exact fun a => ⟨hA a, hB a⟩

/-! ## Surjectivity -/

/-! ### R5. `Function.Surjective f` · `unfold Function.Surjective at hf` · context: the definition appears
`Function.Surjective f` is defined as `∀ b, ∃ a, f a = b`. `choose` looks through the name by itself,
so this step is only for reading; `choose g hg using hf` works without it. -/
example {α β : Type} (f : α → β) (hf : Function.Surjective f) (G : Prop)
    (h : (∀ b, ∃ a, f a = b) → G) : G := by
  unfold Function.Surjective at hf
  exact h hf

/-! ## One `∃` at the term level -/

/-! ### R6. `Exists.choose` · `h.choose : α` for `h : ∃ a, Q a` · a term: the witness itself
It uses the axiom of choice, so a `def` built from it must be marked `noncomputable`: without the
keyword Lean reports "failed to compile definition, consider marking it as 'noncomputable'".
Inside a proof no keyword is needed: `h.choose` is an `α` you can pass wherever an `α` is expected. -/
noncomputable def wit {α : Type} {Q : α → Prop} (h : ∃ a, Q a) : α := h.choose

example {α : Type} (Q P : α → Prop) (h : ∃ a, Q a) (hP : ∀ a, P a) : P h.choose := by
  exact hP h.choose

/-! ### R7. `unfold wit` · goal: the name `wit h` → its body `h.choose` -/
example {α : Type} (Q P : α → Prop) (h : ∃ a, Q a) (hp : P h.choose) : P (wit h) := by
  unfold wit
  exact hp

/-! ### R8. `Exists.choose_spec` · `h.choose_spec : Q h.choose` · closes `Q h.choose`
The witness `h.choose` has the property `h` promised. -/
example {α : Type} (Q : α → Prop) (h : ∃ a, Q a) : Q h.choose := by
  exact h.choose_spec

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1 then R2 in one line: a function `g` with `n < g n * g n` -/
example (h : ∀ n : ℕ, ∃ m, n < m * m) : ∃ g : ℕ → ℕ, ∀ n, n < g n * g n := by
  choose g hg using h
  exact ⟨g, hg⟩

/-! ### W2. Two `∀`s and an `∧`: `choose` makes a two-argument function (R3, R4) -/
example (h : ∀ a b : ℕ, ∃ c, a ≤ c ∧ b ≤ c) : ∃ g : ℕ → ℕ → ℕ, ∀ a b, a ≤ g a b ∧ b ≤ g a b := by
  choose g hA hB using h
  exact ⟨g, fun a b => ⟨hA a b, hB a b⟩⟩

/-! ### W3. `choose` straight on a `Function.Surjective` hypothesis (R5, R1), then use `hg y` -/
example (f : ℤ → ℤ) (hf : Function.Surjective f) : ∃ g : ℤ → ℤ, ∀ y, f (g y) + 1 = y + 1 := by
  choose g hg using hf
  exact ⟨g, fun y => by rw [hg y]⟩

/-! ### W4. Term mode sees through a `def`: `wit h` is `h.choose` by definition, so R8 fits directly -/
example (h : ∃ n : ℕ, n + n = 10) : wit h + wit h = 10 := h.choose_spec

end E090Guide

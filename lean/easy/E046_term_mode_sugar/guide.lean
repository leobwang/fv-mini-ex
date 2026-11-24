/- Guide for E046 (Term-mode sugar).
Part R: one reference entry per piece of term syntax or library lemma the exercise needs, stated with
typed placeholders. This exercise bans tactic blocks, so every entry is a term: there is no tactic
state to step through. To see what a spot expects, replace the term there by `_` in a scratch copy:
Lean's error "don't know how to synthesize placeholder" lists the context and, after the turnstile,
the expected type. cheatsheet.md shows those expected types before and after each step.
`A B C : Prop` are arbitrary propositions, `P : α → Prop` is "the rest of the statement", and a
hypothesis such as `k` or `f` in an entry is only there to finish the example.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033), in particular E004 (term-mode proofs).
-/

namespace E046Guide

/-! # Part R · Reference entries -/

/-! ## Dot notation on hypotheses -/

/-! ### R1. `h.elim f g` (`Or.elim`) · `h : A ∨ B` turns the expected `C` into two functions
`Or.elim : a ∨ b → (a → c) → (b → c) → c`. Dot notation: `h : A ∨ B` has type `Or A B`, so `h.elim`
means `Or.elim h`; `f` handles the left case, `g` the right one. -/
example {A B C : Prop} (h : A ∨ B) (f : A → C) (g : B → C) : C :=
  h.elim f g

/-! ### R2. `h.mp`, `h.mpr` (`Iff.mp`, `Iff.mpr`) · an `↔` used as a function, in either direction
`Iff.mp : (a ↔ b) → a → b`, `Iff.mpr : (a ↔ b) → b → a`. On its own, `h.mp` is a function `A → B`,
so it can be passed wherever an `A → B` is expected (as the `f` of R1). -/
example {A B : Prop} (h : A ↔ B) (ha : A) : B :=
  h.mp ha

example {A B : Prop} (h : A ↔ B) (hb : B) : A :=
  h.mpr hb

/-! ## Naming a hypothesis by its type -/

/-! ### R3. `‹T›` · "the hypothesis of type `T`", found in the context
`‹T›` (typed `\f<` and `\f>`) stands for a proof of `T` that is already in the context; its name does
not matter. It fails if no hypothesis has exactly type `T`. -/
example {A B : Prop} (ha : A) (f : A → B) : B :=
  f ‹A›

/-! ## Chaining `↔` -/

/-! ### R4. `h1.trans h2` (`Iff.trans`) · `A ↔ B` and `B ↔ C` give `A ↔ C`
`Iff.trans : (a ↔ b) → (b ↔ c) → (a ↔ c)`. Dot notation again: `h1.trans h2 = Iff.trans h1 h2`.
It chains: `(h1.trans h2).trans h3`. -/
example {A B C D : Prop} (h1 : A ↔ B) (h2 : B ↔ C) (h3 : C ↔ D) : A ↔ D :=
  (h1.trans h2).trans h3

/-! ## Equalities: computation and substitution -/

/-! ### R5. `rfl` · closes `s = t` when both sides compute to the same value
`rfl : a = a`. Lean accepts it for `s = t` when `s` and `t` reduce to the same term, so closed `Nat`
arithmetic such as `2 * 3 + 1 = 7` holds by `rfl`. With a variable, `m + m = 6` does not. -/
example : 2 * 3 + 1 = 7 :=
  rfl

/-! ### R6. `h ▸ e` · with `h : a = b`, rewrites the expected type by `h`, then checks `e` against it
Typed `\t`. Here the expected type `P a` becomes `P b`, which `hb` proves. `▸` tries `h` in both
directions, so `h : b = a` works as well. When the expected type is unknown, it rewrites the type of
`e` instead. -/
example {α : Type} (a b : α) (P : α → Prop) (h : a = b) (hb : P b) : P a :=
  h ▸ hb

/-! ## Taking apart and building `∃` -/

/-! ### R7. `let ⟨x, hx⟩ := h; e` · context gains the witness `x` and its proof `hx`
Destructures `h : ∃ x, p x` inside a term; `e` is then checked with `x : α` and `hx : p x` in the
context. Allowed because the expected type is a `Prop`. Patterns nest and flatten: `⟨x, ha, hb⟩` is
`⟨x, ⟨ha, hb⟩⟩`, so it also splits `p x ∧ r x`; write `_` for a part you do not need. -/
example {α : Type} {A : Prop} (p : α → Prop) (h : ∃ x, p x) (k : ∀ x, p x → A) : A :=
  let ⟨x, hx⟩ := h
  k x hx

example {α : Type} {A : Prop} (p r : α → Prop) (h : ∃ x, p x ∧ r x) (k : ∀ x, r x → A) : A :=
  let ⟨x, _, hr⟩ := h
  k x hr

/-! ### R8. `⟨w, hw⟩` · builds `∃ x, p x` from a witness `w` and a proof `hw : p w`
The anonymous constructor: here it means `Exists.intro w hw`. -/
example {α : Type} (p : α → Prop) (w : α) (hw : p w) : ∃ x, p x :=
  ⟨w, hw⟩

/-! ## Intermediate facts inside a term -/

/-! ### R9. `have h : T := e` then the rest on the next line · context gains `h : T`
The expected type of the rest is unchanged. `;` instead of a line break also works. -/
example {A B C : Prop} (ha : A) (f : A → B) (g : B → C) : C :=
  have hb : B := f ha
  g hb

/-! ### R10. `Nat.le_trans` · `n ≤ m → m ≤ k → n ≤ k` -/
example (x y z : Nat) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z :=
  Nat.le_trans hxy hyz

/-! ### R11. `show T from e` · replaces the expected type by `T` (they must agree by
computation), then checks `e` against `T`
`m.succ` (`Nat.succ m`) and `m + 1` compute to the same thing, so here `T` may be either. -/
example (n m : Nat) (h : n ≤ m.succ) : n ≤ m + 1 :=
  show n ≤ m.succ from h

/-! ### R12. `Nat.le_succ_of_le` · `n ≤ m → n ≤ m.succ`; also accepted for `n ≤ m + 1` -/
example (x y : Nat) (h : x ≤ y) : x ≤ y + 1 :=
  Nat.le_succ_of_le h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R1 with R2: an `↔` passed as one case of the `∨` -/
example {A B C : Prop} (h : A ∨ B) (hca : C ↔ A) (hbc : B → C) : C :=
  h.elim hca.mpr hbc

/-! ### W2. R6 with R5: substitute, then compute -/
example (m : Nat) (h : m = 3) : m * m = 9 :=
  h ▸ rfl

/-! ### W3. R7 with R8: take a pair apart and put it back in the other order -/
example (s t : Nat → Prop) (h : ∃ k, s k ∧ t k) : ∃ k, t k ∧ s k :=
  let ⟨k, hs, ht⟩ := h
  ⟨k, ht, hs⟩

/-! ### W4. R9, R12, R11, R12: two steps up, with the intermediate fact named -/
example (x y : Nat) (h : x ≤ y) : x ≤ y + 2 :=
  have h1 : x ≤ y + 1 := Nat.le_succ_of_le h
  show x ≤ y + 2 from Nat.le_succ_of_le h1

end E046Guide

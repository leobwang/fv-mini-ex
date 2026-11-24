/- Guide for E004 (Term-mode proofs).
Part R: one reference entry per piece of term syntax the exercise needs, stated with typed
placeholders. This exercise bans tactic blocks, so every entry is a term: there is no tactic state to
step through. What plays the role of the goal is the EXPECTED TYPE, the type the term at a given spot
must have. To see it, replace a term by `_` in a scratch copy: Lean's error "don't know how to
synthesize placeholder" lists the context and, after the turnstile `⊢`, the expected type at that `_`.
cheatsheet.md shows those expected types before and after each step.
`A B C G : Prop` are arbitrary propositions; a hypothesis such as `k` or `f` in an entry is only there
to finish the example.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001 (`theorem`/`example`, `rfl`), E002 (`def`), E003 (`intro`, `exact`, `apply`, and a
proof of `A → B` used as a function).
-/

namespace E004Guide

/-! # Part R · Reference entries -/

/-! ## Proving an implication: `fun` -/

/-! ### R1. `fun h => e` · expected `A → B` → context gains `h : A`, expected type of `e` is `B`
A proof of `A → B` is a function from proofs of `A` to proofs of `B`. `fun h => e` is that function:
the term-mode form of `intro h` (E003). `=>` is typed as two characters `=` `>`. -/
example (A B : Prop) (k : A → B) : A → B :=
  fun h => k h

/-! ## Building and taking apart `∧` -/

/-! ### R2. `⟨a, b⟩` (`And.intro`) · expected `A ∧ B` → two holes, expecting `A` and `B`
The anonymous constructor (typed `\<` and `\>`): it means `And.intro a b`, where
`And.intro : a → b → a ∧ b`. The components can be any terms, applications included. -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B :=
  ⟨ha, hb⟩

/-! ### R3. `fun ⟨ha, hb⟩ => e` · expected `A ∧ B → G` → context gains `ha : A`, `hb : B`
A pattern in a `fun` takes the pair apart as it is bound: no name for the pair itself, no `.1`/`.2`.
Write `_` for a component you do not need. The pair stays in the context, unnamed, as `x✝`. -/
example (A B : Prop) : A ∧ B → A :=
  fun ⟨ha, _⟩ => ha

/-! ## More premises, and using an implication -/

/-! ### R4. `fun h1 h2 h3 => e` · one name per `→`, left to right; context gains all three
`A → B → C → G` is `A → (B → (C → G))` (`→` nests to the right), so one `fun` with three names
binds all three premises: the term-mode form of `intro h1 h2 h3`. -/
example (A B C G : Prop) (k : A → B → C → G) : A → B → C → G :=
  fun h1 h2 h3 => k h1 h2 h3

/-! ### R5. `f a`, `f a b` · closes `B` from `f : A → B` and `a : A`
Applying a proof of an implication to a proof of its premise gives a proof of its conclusion (the
term-mode form of `exact f a`). Arguments are separated by spaces, in the order of `f`'s premises:
`f : A → B → C` applied as `f a b`. Written with holes, `f _ _`, each hole expects one premise. -/
example (A B : Prop) (f : A → B) (a : A) : B :=
  f a

example (A B C : Prop) (f : A → B → C) (a : A) (b : B) : C :=
  f a b

/-! ## Projections -/

/-! ### R6. `h.1`, `h.2` (`And.left`, `And.right`) · from `h : A ∧ B`, a proof of `A`, of `B`
A proof of `A ∧ B` is a pair; `.1` and `.2` are its components. `h.1` is `And.left h` with
`And.left : a ∧ b → a`, and `h.2` is `And.right h`. There is no `h.3`. -/
example (A B : Prop) (h : A ∧ B) : A :=
  h.1

example (A B : Prop) (h : A ∧ B) : B :=
  h.2

/-! ## Using `↔` -/

/-! ### R7. `h.1 a`, `h.2 b` (`Iff.mp`, `Iff.mpr`) · from `h : A ↔ B`, a function `A → B`, `B → A`
`A ↔ B` is a pair of implications. `h.1` is `Iff.mp h : A → B` (left to right), `h.2` is
`Iff.mpr h : B → A` (right to left); apply them as in R5. -/
example (A B : Prop) (h : A ↔ B) (a : A) : B :=
  h.1 a

example (A B : Prop) (h : A ↔ B) (b : B) : A :=
  h.2 b

/-! ## Nesting applications -/

/-! ### R8. `f (g a)` · an argument that is itself an application needs parentheses
`f g a` means `(f g) a`: it passes the FUNCTION `g` to `f`, a type error. Parenthesize the inner
application. A term such as `g a` may appear more than once in one proof: proofs are values, and
using one does not use it up. -/
example (A B C : Prop) (f : B → C) (g : A → B) (a : A) : C :=
  f (g a)

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. R3 with a nested pattern, then R2: `A ∧ B ∧ C` is `A ∧ (B ∧ C)`, and `⟨ha, _, hc⟩`
is `⟨ha, ⟨_, hc⟩⟩` -/
example (A B C : Prop) : A ∧ B ∧ C → C ∧ A :=
  fun ⟨ha, _, hc⟩ => ⟨hc, ha⟩

/-! ### W2. R3, R2 and R5: apply one function to each component -/
example (A B C G : Prop) (f : A → B) (g : C → G) : A ∧ C → B ∧ G :=
  fun ⟨ha, hc⟩ => ⟨f ha, g hc⟩

/-! ### W3. R1, R2, R7: a pair whose first component comes through an `↔`, read right to left -/
example (A B : Prop) (h : A ↔ B) : B → A ∧ B :=
  fun hb => ⟨h.2 hb, hb⟩

/-! ### W4. R2 with R6 twice: `h.2.2` is `(h.2).2`, the third component of `A ∧ (B ∧ C)` -/
example (A B C : Prop) (h : A ∧ B ∧ C) : C ∧ A :=
  ⟨h.2.2, h.1⟩

end E004Guide

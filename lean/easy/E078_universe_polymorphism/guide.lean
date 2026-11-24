/- Guide for E078 (Universe polymorphism).
Part R: one reference entry per tactic, piece of syntax or universe fact the exercise needs, stated with
typed placeholders. Put the cursor before and after the step to see the proof state change in the
infoview. `P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use three small functions of their own, `idS`, `swapU` and `dup`; they are not the
exercise's `mapFst` / `pick`.
Part W: worked combinations on `swapU`, `Option` and `id`.
Assumed: Lean basics (E001–E033).
-/

namespace E078Guide

/-! # Part R · Reference entries -/

/-! ## Universe variables and building a pair (a `def` body) -/

/-! ### R1. `universe u v` and `{α : Type u}` · context: `α` is a type at level `u`
`universe u v` declares two universe variables (levels `0, 1, 2, …`). `Type u` is the universe at level
`u`: `Type 0` (written `Type`) holds `Nat`, `Bool`, `List Nat`; `Type 1` holds `Type` itself; and so on.
A binder `{α : Type u}` makes the declaration work at every level at once. Writing a `def` body with
`by` shows its context (the binders) and its goal (the result type). -/
universe u v

example {α : Type u} {β : Type v} (P : α → β → Prop) (a : α) (b : β) (h : P a b) : P a b := by
  exact h

/-! ### R2. `(x, y)` · closes a goal `α × β`: the anonymous pair constructor `Prod.mk x y` -/
example {α : Type u} {β : Type v} (a : α) (b : β) : α × β := by
  exact (a, b)

/-! ### R3. `p.1`, `p.2` · the projections `Prod.fst p : α`, `Prod.snd p : β` close a goal `α` or `β`
The infoview prints them as `p.fst`, `p.snd`. -/
example {α : Type u} {β : Type v} (p : α × β) : β := by
  exact p.2

/-! ### R4. `f a` · applying `f : α → γ` to `a : α` closes a goal `γ` (any term of type `α` works as `a`) -/
example {α γ : Type u} (f : α → γ) (a : α) : γ := by
  exact f a

/-! ## `Sort u`: one binder for propositions and types -/

/-! ### R5. `{α : Sort u}` · also accepts proofs: `Sort 0 = Prop`, `Sort (u + 1) = Type u`
`idS` below is declared once for `Sort u`. At a proof `hp : p` (with `p : Prop = Sort 0`) it takes
`α := p`, so `u := 0`. At the type `Nat` it takes `α := Type`, and `Type = Sort 1 : Sort 2`, so `u := 2`
(printed `idS.{2}`). A binder `{α : Type u}` could not take a proof: `Type u` is never `Prop`.
`set_option pp.universes true in` makes the infoview print the levels Lean chose (`.{2}`). -/
def idS {α : Sort u} (a : α) : α := a

example (p : Prop) (hp : p) : p := by
  exact idS hp

set_option pp.universes true in
example : idS Nat = Nat := by
  rfl

/-! ## Why `rfl` proves the theorems: the definitional steps one at a time -/

/-- `swapU p` swaps the two components of a pair. -/
def swapU {α : Type u} {β : Type v} (p : α × β) : β × α := (p.2, p.1)

/-! ### R6. `unfold f` · goal: `f x` → the body of `f` with `x` substituted -/
example {α : Type u} {β : Type v} (p : α × β) (P : β × α → Prop) (h : P (p.2, p.1)) :
    P (swapU p) := by
  unfold swapU
  exact h

/-! ### R7. `dsimp only` · goal: a projection of a literal pair computes, `(a, b).1` → `a` -/
example {α : Type u} {β : Type v} (a : α) (b : β) (P : α → Prop) (h : P a) : P (a, b).1 := by
  dsimp only
  exact h

/-! ### R8. `dsimp only [id]` · goal: `id x` → `x` (`id : α → α` is the identity function) -/
example {α : Type u} (a : α) (P : α → Prop) (h : P a) : P (id a) := by
  dsimp only [id]
  exact h

/-! ### R9. `rfl` · closes `(p.1, p.2) = p`: rebuilding a pair from its projections is `p` itself
(structure eta: Lean identifies the two by definition, for any structure). -/
example {α : Type u} {β : Type v} (p : α × β) : (p.1, p.2) = p := by
  rfl

/-! ### R10. `rfl` · closes `s = t` whenever both sides unfold to the same term
It performs R6–R9 and R11 by itself, so a goal that holds "by the definitions" needs no other step. -/
example {α : Type u} {β : Type v} (a : α) (b : β) : swapU (a, b) = (b, a) := by
  rfl

/-! ### R11. `dsimp only [Function.comp]` · goal: `(g ∘ f) x` → `g (f x)`
`g ∘ f` is `Function.comp g f`, "first `f`, then `g`". -/
example {α β γ : Type u} (f : α → β) (g : β → γ) (a : α) (P : γ → Prop) (h : P (g (f a))) :
    P ((g ∘ f) a) := by
  dsimp only [Function.comp]
  exact h

/-! ## Types as values: which universe Lean picks -/

/-! ### R12. `Type : Type 1`, and a pair type lives at the larger level · goal `Type 1` closed by a type
`α × β` with `α : Type u`, `β : Type v` lives in `Type (max u v)`. So `Type × Nat` (pairs whose first
component is a type) lives in `Type 1`, and so does `Type → Type` (the type of `List` and `Option`). -/
example : Type 1 := by
  exact Type × Nat

example : Type 1 := by
  exact Type → Type

/-! ### R13. Instantiating a universe: `α := Type` forces `u := 1` · `rfl` closes the goal
`dup` below is declared once for `Type u`. Applied to the type `Nat`, Lean takes `α := Type`, and since
`Type : Type 1`, it picks `u := 1`: `dup.{1}`. `Eq.{2}` says the equation compares two terms of a type in
`Sort 2 = Type 1` (here `Type × Type`). -/
def dup {α : Type u} (a : α) : α × α := (a, a)

set_option pp.universes true in
example : dup Nat = (Nat, Nat) := by
  rfl

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A theorem by unfolding (R6), then `rfl` computes the projections (R7) and uses eta (R9);
`dsimp only` would also close the goal after `unfold`, and `rfl` alone does all of it (R10) -/
example {α : Type u} {β : Type v} (p : α × β) : swapU (swapU p) = p := by
  unfold swapU
  rfl

example {α : Type u} {β : Type v} (p : α × β) : swapU (swapU p) = p := by
  rfl

/-! ### W2. `swapU` on a pair of types: `α := Type`, `β := Type`, so `u := 1`, `v := 1` (R12, R13) -/
set_option pp.universes true in
example : swapU (Nat, Bool) = (Bool, Nat) := by
  rfl

/-! ### W3. A type constructor as an ordinary function: `Option : Type → Type`, composed with `id`
(R8, R11) -/
example : (Option ∘ id) Nat = Option Nat := by
  dsimp only [Function.comp, id]

end E078Guide
